use crate::{
    codegen::{
        expression::ExpressionEvaluator,
        pcs::{queries, rotation_sets},
        template::{Halo2Verifier, Halo2VerifyingKey},
    },
    fe_to_u256, g1_to_u256, g2_to_u256,
};
use halo2_proofs::{
    arithmetic::Field,
    halo2curves::{ff::PrimeField, pairing::MultiMillerLoop, serde::SerdeObject, CurveAffine},
    plonk::{Gate, VerifyingKey},
    poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG, Rotation},
};
use itertools::{chain, izip, Itertools};
use ruint::aliases::U256;
use std::{
    collections::BTreeMap,
    fmt::{self, Debug},
    iter,
};

mod expression;
mod pcs;
mod template;

#[derive(Debug)]
pub struct SolidityGenerator<'a, C: CurveAffine> {
    vk: &'a VerifyingKey<C>,
    num_instances: usize,
    acc_encoding: Option<AccumulatorEncoding>,
    g1: [U256; 2],
    g2: [U256; 4],
    s_g2: [U256; 4],
}

#[derive(Clone, Copy, Debug)]
pub struct AccumulatorEncoding {
    pub offset: usize,
    pub num_limbs: usize,
    pub num_limb_bits: usize,
}

impl<'a, C: CurveAffine> SolidityGenerator<'a, C> {
    pub fn new<M: MultiMillerLoop<G1Affine = C>>(
        param: &ParamsKZG<M>,
        vk: &'a VerifyingKey<C>,
        num_instances: usize,
        acc_encoding: Option<AccumulatorEncoding>,
    ) -> Self
    where
        C::Base: PrimeField<Repr = [u8; 0x20]>,
        M: Debug,
        M::Scalar: PrimeField,
        M::G1Affine: SerdeObject,
        M::G2Affine: SerdeObject,
    {
        assert_eq!(vk.cs().num_instance_columns(), 1);
        assert!(!vk
            .cs()
            .instance_queries()
            .iter()
            .any(|(_, rotation)| *rotation != Rotation::cur()));

        let g1 = param.get_g()[0];
        let g1 = g1_to_u256(g1);
        let g2 = g2_to_u256(param.g2());
        let s_g2 = g2_to_u256(-param.s_g2());

        Self {
            vk,
            num_instances,
            acc_encoding,
            g1,
            g2,
            s_g2,
        }
    }
}

impl<'a, C: CurveAffine> SolidityGenerator<'a, C>
where
    C::Base: PrimeField<Repr = [u8; 0x20]>,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
{
    pub fn generate(&self, _: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        todo!()
    }

    pub fn generate_separately(
        &self,
        vk_writer: &mut impl fmt::Write,
        verifier_writer: &mut impl fmt::Write,
    ) -> Result<(), fmt::Error> {
        let (vk, verifier) = self.generate_inner();

        vk.render(vk_writer)?;
        verifier.render(verifier_writer)?;

        Ok(())
    }

    fn generate_inner(&self) -> (Halo2VerifyingKey, Halo2Verifier) {
        let num_neg_lagranges = self.vk.cs().blinding_factors() + 1;
        let num_quotients = self.vk.get_domain().get_quotient_poly_degree();
        let (num_constants, vk_chunks) = {
            let domain = self.vk.get_domain();
            let digest = fe_to_u256(self.vk.transcript_repr());
            let k = U256::from(domain.k());
            let n_inv = fe_to_u256(C::Scalar::from(1 << domain.k()).invert().unwrap());
            let omega = fe_to_u256(domain.get_omega());
            let omega_inv = fe_to_u256(domain.get_omega_inv());
            let omega_inv_to_l = fe_to_u256(
                domain
                    .get_omega_inv()
                    .pow_vartime([num_neg_lagranges as u64]),
            );
            let num_instances = U256::from(self.num_instances);
            let fixed_commitments = self.vk.fixed_commitments().iter().flat_map(g1_to_u256::<C>);
            let permutation_commitments = self
                .vk
                .permutation()
                .commitments()
                .iter()
                .flat_map(g1_to_u256::<C>);
            let constants = chain![
                [
                    digest,
                    k,
                    n_inv,
                    omega,
                    omega_inv,
                    omega_inv_to_l,
                    num_instances,
                    U256::from(self.acc_encoding.is_some()),
                    self.acc_encoding
                        .map(|acc_encoding| U256::from(acc_encoding.offset))
                        .unwrap_or_default(),
                    self.acc_encoding
                        .map(|acc_encoding| U256::from(acc_encoding.num_limbs))
                        .unwrap_or_default(),
                    self.acc_encoding
                        .map(|acc_encoding| U256::from(acc_encoding.num_limb_bits))
                        .unwrap_or_default(),
                ],
                self.g1,
                self.g2,
                self.s_g2
            ]
            .collect_vec();
            (
                constants.len(),
                chain![constants, fixed_commitments, permutation_commitments,].collect_vec(),
            )
        };
        let permutation_columns = self.vk.cs().permutation().get_columns();
        let permutation_chunk_len = self.vk.cs().degree() - 2;
        let num_permutation_zs = permutation_columns.chunks(permutation_chunk_len).count();
        let (max_phase, num_witnesses, num_challenges) = {
            let (max_phase, mut num_witnesses) = {
                let counts = self.vk.cs().advice_column_phase().iter().cloned().counts();
                let max_phase = *counts.keys().max().unwrap();
                (
                    max_phase,
                    (0..=max_phase).map(|phase| counts[&(phase)]).collect_vec(),
                )
            };
            let mut num_challenges = {
                let counts = self.vk.cs().challenge_phase().iter().cloned().counts();
                (0..=max_phase)
                    .map(|phase| counts.get(&phase).copied().unwrap_or_default())
                    .collect_vec()
            };

            *num_challenges.last_mut().unwrap() += 1; // theta

            num_witnesses.push(2 * self.vk.cs().lookups().len()); // lookup permuted
            num_challenges.push(2); // beta, gamma

            num_witnesses.push(num_permutation_zs + self.vk.cs().lookups().len() + 1); // grand products, random
            num_challenges.push(1); // y

            num_witnesses.push(num_quotients); // quotients
            num_challenges.push(1); // x

            (max_phase as usize, num_witnesses, num_challenges)
        };
        let num_evals = self.vk.cs().fixed_queries().len()
            + self.vk.cs().advice_queries().len()
            + 1
            + self.vk.cs().permutation().get_columns().len()
            + (3 * num_permutation_zs - 1)
            + 5 * self.vk.cs().lookups().len();
        let proof_len = 0x40 * num_witnesses.iter().sum::<usize>() + 0x20 * num_evals + 0x40 * 2;

        let proof_cptr = 0x84;
        let quotient_cptr = proof_cptr + 0x40 * num_witnesses.iter().rev().skip(1).sum::<usize>();
        let eval_cptr = proof_cptr + 0x40 * num_witnesses.iter().sum::<usize>();
        let w_cptr = eval_cptr + num_evals * 0x20;
        let w_prime_cptr = w_cptr + 0x40;

        let vk_mptr = {
            let (superset, rotation_sets) = rotation_sets(&queries(self.vk, proof_cptr, 0x10000));
            let num_weights = rotation_sets
                .iter()
                .map(|set| set.rotations().len())
                .sum::<usize>();
            itertools::max(chain![
                num_witnesses.iter().map(|n| (n * 0x40) + 0x20),
                [
                    (num_evals + 1) * 0x20,
                    (num_weights + 1) * 0x20 * 2
                        + 7 * 0x20
                        + superset.len() * 3 * 0x20
                        + rotation_sets.len() * 2 * 0x20
                ],
            ])
            .unwrap()
        };
        let fixed_comm_mptr = vk_mptr + 0x20 * num_constants;
        let vk_len = 0x20 * vk_chunks.len();
        let challenge_mptr = vk_mptr + vk_len;
        let theta_mptr =
            challenge_mptr + 0x20 * (num_challenges[..=max_phase].iter().sum::<usize>() - 1);
        let instance_eval_mptr = theta_mptr + 8 * 0x20;

        let mut evaluator = ExpressionEvaluator::new(self.vk.cs(), challenge_mptr, eval_cptr);
        let gate_computations = self
            .vk
            .cs()
            .gates()
            .iter()
            .flat_map(Gate::polynomials)
            .map(|expression| evaluator.evaluate_and_reset(expression))
            .collect_vec();
        let permutation_computations = chain![
            evaluator.permutation_z_eval_asm.first().map(|asm| {
                vec![
                    "let l_0 := mload(L_0_MPTR)".to_string(),
                    format!("let perm_z_0 := {}", asm.0),
                    "let eval := addmod(l_0, sub(r, mulmod(l_0, perm_z_0, r)), r)".to_string(),
                ]
            }),
            evaluator.permutation_z_eval_asm.last().map(|asm| {
                let item = "addmod(mulmod(perm_z_last, perm_z_last, r), sub(r, perm_z_last), r)";
                vec![
                    "let l_last := mload(L_LAST_MPTR)".to_string(),
                    format!("let perm_z_last := {}", asm.0),
                    format!("let eval := mulmod(l_last, {item}, r)"),
                ]
            }),
            izip!(
                &evaluator.permutation_z_eval_asm,
                &evaluator.permutation_z_eval_asm[1..]
            )
            .map(|(asm, asm_next)| {
                vec![
                    "let l_0 := mload(L_0_MPTR)".to_string(),
                    format!("let perm_z_i_last := {}", asm.2),
                    format!("let perm_z_j := {}", asm_next.0),
                    "let eval := mulmod(l_0, addmod(perm_z_j, sub(r, perm_z_i_last), r), r)"
                        .to_string(),
                ]
            }),
            izip!(
                permutation_columns.chunks(permutation_chunk_len),
                &evaluator.permutation_z_eval_asm,
            )
            .enumerate()
            .map(|(chunk_idx, (columns, asm))| {
                chain![
                    [
                        "let gamma := mload(GAMMA_MPTR)".to_string(),
                        format!("let left := {}", asm.1),
                        format!("let right := {}", asm.0),
                        "let tmp".to_string(),
                    ],
                    columns.iter().flat_map(|column| {
                        let item = format!(
                            "mulmod(mload(BETA_MPTR), {}, r)",
                            evaluator.permutation_eval_asm[column],
                        );
                        [
                            format!(
                                "tmp := addmod(addmod({}, {item}, r), gamma, r)",
                                evaluator.eval_asm(column),
                            ),
                            "left := mulmod(left, tmp, r)".to_string(),
                        ]
                    }),
                    columns.iter().enumerate().flat_map(|(idx, column)| {
                        chain![
                            (chunk_idx == 0 && idx == 0).then(|| {
                                "mstore(0x00, mulmod(mload(BETA_MPTR), mload(X_MPTR), r))"
                                    .to_string()
                            }),
                            [
                                format!(
                                    "tmp := addmod(addmod({}, mload(0x00), r), gamma, r)",
                                    evaluator.eval_asm(column),
                                ),
                                "right := mulmod(right, tmp, r)".to_string(),
                            ],
                            (!(chunk_idx == num_permutation_zs - 1 && idx == columns.len() - 1))
                                .then(|| "mstore(0x00, mulmod(mload(0x00), delta, r))".to_string()),
                        ]
                    }),
                    {
                        let item = "sub(r, mulmod(left_sub_right, addmod(l_last, l_blind, r), r))";
                        [
                            "let l_blind := mload(L_BLIND_MPTR)".to_string(),
                            "let l_last := mload(L_LAST_MPTR)".to_string(),
                            "let left_sub_right := addmod(left, sub(r, right), r)".to_string(),
                            format!("let eval := addmod(left_sub_right, {item}, r)"),
                        ]
                    }
                ]
                .collect_vec()
            })
        ]
        .zip(iter::repeat_with(|| "eval".to_string()))
        .collect_vec();
        let lookup_computations = {
            let input_tables = self
                .vk
                .cs()
                .lookups()
                .iter()
                .map(|lookup| {
                    let (input_lines, inputs) = lookup
                        .input_expressions()
                        .iter()
                        .map(|expression| evaluator.evaluate(expression))
                        .fold((Vec::new(), Vec::new()), |mut acc, result| {
                            acc.0.extend(result.0);
                            acc.1.push(result.1);
                            acc
                        });
                    evaluator.reset();
                    let (table_lines, tables) = lookup
                        .table_expressions()
                        .iter()
                        .map(|expression| evaluator.evaluate(expression))
                        .fold((Vec::new(), Vec::new()), |mut acc, result| {
                            acc.0.extend(result.0);
                            acc.1.push(result.1);
                            acc
                        });
                    evaluator.reset();
                    (input_lines, inputs, table_lines, tables)
                })
                .collect_vec();
            izip!(input_tables, &evaluator.lookup_eval_asm)
                .flat_map(|((input_lines, inputs, table_lines, tables), asm)| {
                    [
                        vec![
                            "let l_0 := mload(L_0_MPTR)".to_string(),
                            format!(
                                "let eval := addmod(l_0, mulmod(l_0, sub(r, {}), r), r)",
                                asm.0
                            ),
                        ],
                        {
                            let item = format!(
                                "addmod(mulmod({}, {}, r), sub(r, {}), r)",
                                asm.0, asm.0, asm.0
                            );
                            vec![
                                "let l_last := mload(L_LAST_MPTR)".to_string(),
                                format!("let eval := mulmod(l_last, {item}, r)"),
                            ]
                        },
                        chain![
                            [
                                "let theta := mload(THETA_MPTR)",
                                "let beta := mload(BETA_MPTR)",
                                "let gamma := mload(GAMMA_MPTR)",
                                "let input",
                                "{"
                            ]
                            .map(str::to_string),
                            chain![
                                input_lines,
                                [format!("input := {}", &inputs[0])],
                                inputs[1..].iter().flat_map(|input| [
                                    "input := mulmod(input, theta, r)".to_string(),
                                    format!("input := addmod(input, {input}, r)"),
                                ])
                            ]
                            .map(|line| format!("    {line}")),
                            ["}".to_string()],
                            ["let table", "{"].map(str::to_string),
                            chain![
                                table_lines,
                                [format!("table := {}", &tables[0])],
                                tables[1..].iter().flat_map(|table| [
                                    "table := mulmod(table, theta, r)".to_string(),
                                    format!("table := addmod(table, {table}, r)"),
                                ])
                            ]
                            .map(|line| format!("    {line}")),
                            ["}".to_string()],
                            {
                                let permuted = format!(
                                    "mulmod(addmod({}, beta, r), addmod({}, gamma, r), r)",
                                    asm.2, asm.4
                                );
                                let input =
                                    "mulmod(addmod(input, beta, r), addmod(table, gamma, r), r)";
                                [
                                    format!("let left := mulmod({}, {permuted}, r)", asm.1),
                                    format!("let right := mulmod({}, {input}, r)", asm.0),
                                ]
                            },
                            [
                                "let l_blind := mload(L_BLIND_MPTR)",
                                "let l_last := mload(L_LAST_MPTR)",
                                "let l_active := addmod(1, sub(r, addmod(l_last, l_blind, r)), r)",
                                "let eval := mulmod(l_active, addmod(left, sub(r, right), r), r)"
                            ]
                            .map(str::to_string),
                        ]
                        .collect_vec(),
                        vec![
                            "let l_0 := mload(L_0_MPTR)".to_string(),
                            format!(
                                "let eval := mulmod(l_0, addmod({}, sub(r, {}), r), r)",
                                asm.2, asm.4
                            ),
                        ],
                        vec![
                            "let l_blind := mload(L_BLIND_MPTR)".to_string(),
                            "let l_last := mload(L_LAST_MPTR)".to_string(),
                            "let l_active := addmod(1, sub(r, addmod(l_last, l_blind, r)), r)"
                                .to_string(),
                            format!("let eval := l_active"),
                            format!(
                                "eval := mulmod(eval, addmod({}, sub(r, {}), r), r)",
                                asm.2, asm.4
                            ),
                            format!(
                                "eval := mulmod(eval, addmod({}, sub(r, {}), r), r)",
                                asm.2, asm.3
                            ),
                        ],
                    ]
                })
                .zip(iter::repeat_with(|| "eval".to_string()))
                .collect_vec()
        };
        let expression_computations = chain![
            gate_computations,
            permutation_computations,
            lookup_computations
        ]
        .enumerate()
        .map(|(idx, (mut lines, var))| {
            if idx == 0 {
                lines.extend([format!("h_eval_numer := {var}")]);
            } else {
                lines.extend([
                    "h_eval_numer := mulmod(h_eval_numer, y, r)".to_string(),
                    format!("h_eval_numer := addmod(h_eval_numer, {var}, r)"),
                ]);
            }
            lines
        })
        .collect();

        let queries = queries(self.vk, proof_cptr, fixed_comm_mptr);
        let (superset, rotation_sets) = rotation_sets(&queries);

        let pcs_computations = {
            let diff_0_mptr = 0x00;
            let coeff_mptr = rotation_sets
                .iter()
                .scan(diff_0_mptr + 0x20, |state, set| {
                    let mptr = *state;
                    *state += set.rotations().len() * 0x20;
                    Some(mptr)
                })
                .collect_vec();

            let batch_invert_1_end = (1 + rotation_sets
                .iter()
                .map(|set| set.rotations().len())
                .sum::<usize>())
                * 0x20;
            let batch_invert_2_end = rotation_sets.len() * 0x20;
            let free_mptr = batch_invert_1_end * 2 + 6 * 0x20;

            let min_rotation = *superset.first().unwrap();
            let max_rotation = *superset.last().unwrap();
            let point_idx = superset.iter().zip(0..).collect::<BTreeMap<_, _>>();
            let point_mptr = superset
                .iter()
                .zip((free_mptr..).step_by(0x20))
                .collect::<BTreeMap<_, _>>();
            let mu_minus_point_mptr = superset
                .iter()
                .zip((free_mptr + superset.len() * 0x20..).step_by(0x20))
                .collect::<BTreeMap<_, _>>();

            let vanishing_mptr = free_mptr + superset.len() * 2 * 0x20;
            let diff_mptr = vanishing_mptr + 0x20;
            let r_eval_mptr = diff_mptr + rotation_sets.len() * 0x20;
            let sum_mptr = r_eval_mptr + rotation_sets.len() * 0x20;

            chain![
                [
                    chain![
                        [
                            "let x := mload(X_MPTR)",
                            "let omega := mload(OMEGA_MPTR)",
                            "let omega_inv := mload(OMEGA_INV_MPTR)",
                            "let x_pow_of_omega := mulmod(x, omega, r)"
                        ]
                        .map(str::to_string),
                        (1..=max_rotation).flat_map(|rotation| {
                            chain![
                                superset.contains(&rotation).then(|| format!(
                                    "mstore(0x{:x}, x_pow_of_omega)",
                                    point_mptr[&rotation]
                                )),
                                (rotation != max_rotation).then(|| {
                                    "x_pow_of_omega := mulmod(x_pow_of_omega, omega, r)".to_string()
                                })
                            ]
                        }),
                        [
                            format!("mstore(0x{:x}, x)", point_mptr[&0]),
                            "x_pow_of_omega := mulmod(x, omega_inv, r)".to_string()
                        ],
                        (min_rotation..0).rev().flat_map(|rotation| {
                            chain![
                                superset.contains(&rotation).then(|| format!(
                                    "mstore(0x{:x}, x_pow_of_omega)",
                                    point_mptr[&rotation]
                                )),
                                (rotation != min_rotation).then(|| {
                                    "x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)"
                                        .to_string()
                                })
                            ]
                        })
                    ]
                    .collect_vec(),
                    chain![
                        ["let mu := mload(MU_MPTR)", "for", "    {",].map(str::to_string),
                        [
                            format!(
                                "        let mptr := 0x{:x}",
                                free_mptr + superset.len() * 0x20
                            ),
                            format!(
                                "        let mptr_end := 0x{:x}",
                                free_mptr + superset.len() * 2 * 0x20
                            ),
                            format!("        let point_mptr := 0x{free_mptr:x}"),
                        ],
                        [
                            "    }",
                            "    lt(mptr, mptr_end)",
                            "    {}",
                            "{",
                            "    mstore(mptr, addmod(mu, sub(r, mload(point_mptr)), r))",
                            "    mptr := add(mptr, 0x20)",
                            "    point_mptr := add(point_mptr, 0x20)",
                            "}",
                        ]
                        .map(str::to_string),
                        ["let s".to_string()],
                        chain![
                            [format!(
                                "s := mload(0x{:x})",
                                mu_minus_point_mptr[rotation_sets[0].rotations().first().unwrap()]
                            )],
                            rotation_sets[0].rotations().iter().skip(1).map(|rotation| {
                                let item = format!("mload(0x{:x})", mu_minus_point_mptr[rotation]);
                                format!("s := mulmod(s, {item}, r)")
                            }),
                            [format!("mstore(0x{:x}, s)", vanishing_mptr)],
                        ],
                        ["let diff".to_string()],
                        rotation_sets
                            .iter()
                            .zip((diff_mptr..).step_by(0x20))
                            .flat_map(|(set, mptr)| {
                                chain![
                                    [format!(
                                        "diff := mload(0x{:x})",
                                        mu_minus_point_mptr[set.diffs().first().unwrap()]
                                    )],
                                    set.diffs().iter().skip(1).map(|rotation| {
                                        let item =
                                            format!("mload(0x{:x})", mu_minus_point_mptr[rotation]);
                                        format!("diff := mulmod(diff, {item}, r)")
                                    }),
                                    [format!("mstore(0x{:x}, diff)", mptr)],
                                    (mptr == diff_mptr)
                                        .then(|| format!("mstore(0x{diff_0_mptr:x}, diff)")),
                                ]
                            })
                    ]
                    .collect_vec()
                ],
                rotation_sets
                    .iter()
                    .enumerate()
                    .map(|(idx, set)| {
                        let coeff_rotations = set
                            .rotations()
                            .iter()
                            .enumerate()
                            .map(|(i, rotation_i)| {
                                set.rotations()
                                    .iter()
                                    .enumerate()
                                    .filter_map(move |(j, rotation_j)| {
                                        (i != j).then_some((rotation_i, rotation_j))
                                    })
                                    .collect_vec()
                            })
                            .collect_vec();
                        chain![
                            set.rotations().iter().map(|rotation| {
                                format!(
                                    "let point_{} := mload(0x{:x})",
                                    point_idx[rotation], point_mptr[rotation]
                                )
                            }),
                            ["let coeff".to_string()],
                            izip!(
                                set.rotations(),
                                &coeff_rotations,
                                (coeff_mptr[idx]..).step_by(0x20)
                            )
                            .flat_map(
                                |(rotation_i, rotations, mptr)| chain![
                                    [rotations
                                        .first()
                                        .map(|rotation| {
                                            format!(
                                                "coeff := addmod(point_{}, sub(r, point_{}), r)",
                                                point_idx[&rotation.0], point_idx[&rotation.1]
                                            )
                                        })
                                        .unwrap_or_else(|| { "coeff := 1".to_string() })],
                                    rotations.iter().skip(1).map(|(i, j)| {
                                        let item = format!(
                                            "addmod(point_{}, sub(r, point_{}), r)",
                                            point_idx[i], point_idx[j]
                                        );
                                        format!("coeff := mulmod(coeff, {item}, r)")
                                    }),
                                    [
                                        format!(
                                            "coeff := mulmod(coeff, mload(0x{:x}), r)",
                                            mu_minus_point_mptr[rotation_i]
                                        ),
                                        format!("mstore(0x{mptr:x}, coeff)")
                                    ],
                                ]
                            )
                        ]
                        .collect_vec()
                    })
                    .collect_vec(),
                [chain![
                    [
                        format!("success := batch_invert(success, 0x{batch_invert_1_end:x}, r)"),
                        format!("let diff_0_inv := mload(0x{diff_0_mptr:x})"),
                        format!("mstore(0x{diff_mptr:x}, diff_0_inv)"),
                    ],
                    ["for", "    {"].map(str::to_string),
                    [
                        format!("        let mptr := 0x{:x}", diff_mptr + 0x20),
                        format!(
                            "        let mptr_end := 0x{:x}",
                            diff_mptr + rotation_sets.len() * 0x20
                        ),
                    ],
                    [
                        "    }",
                        "    lt(mptr, mptr_end)",
                        "    {}",
                        "{",
                        "    mstore(mptr, mulmod(mload(mptr), diff_0_inv, r))",
                        "    mptr := add(mptr, 0x20)",
                        "}",
                    ]
                    .map(str::to_string),
                ]
                .collect_vec()],
                izip!(
                    0..,
                    &rotation_sets,
                    &coeff_mptr,
                    (r_eval_mptr..).step_by(0x20)
                )
                .map(|(idx, set, coeff_mptr, r_eval_mptr)| {
                    chain![
                        [
                            "let zeta := mload(ZETA_MPTR)".to_string(),
                            "let r_eval := 0".to_string(),
                        ],
                        set.evals()
                            .iter()
                            .enumerate()
                            .rev()
                            .flat_map(|(idx, evals)| {
                                chain![
                                    evals.iter().zip((*coeff_mptr..).step_by(0x20)).map(
                                        |(eval, coeff_mptr)| {
                                            let item = format!(
                                                "mulmod(mload(0x{coeff_mptr:x}), {eval}, r)"
                                            );
                                            format!("r_eval := addmod(r_eval, {item}, r)")
                                        }
                                    ),
                                    (idx != 0)
                                        .then(|| "r_eval := mulmod(r_eval, zeta, r)".to_string()),
                                ]
                            }),
                        (idx != 0).then(|| format!(
                            "r_eval := mulmod(r_eval, mload(0x{:x}), r)",
                            diff_mptr + idx * 0x20
                        )),
                        [format!("mstore(0x{r_eval_mptr:x}, r_eval)")],
                    ]
                    .collect_vec()
                }),
                izip!(&rotation_sets, &coeff_mptr, (sum_mptr..).step_by(0x20)).map(
                    |(set, coeff_mptr, sum_mptr)| {
                        chain![
                            [format!("let sum := mload(0x{coeff_mptr:x})")],
                            (*coeff_mptr..)
                                .step_by(0x20)
                                .take(set.rotations().len())
                                .skip(1)
                                .map(|coeff_mptr| format!(
                                    "sum := addmod(sum, mload(0x{coeff_mptr:x}), r)"
                                )),
                            [format!("mstore(0x{sum_mptr:x}, sum)")],
                        ]
                        .collect_vec()
                    }
                ),
                [
                    chain![
                        ["for", "    {", "        let mptr := 0x00"].map(str::to_string),
                        [
                            format!("        let mptr_end := 0x{:x}", batch_invert_2_end),
                            format!("        let sum_mptr := 0x{:x}", sum_mptr),
                        ],
                        [
                            "    }",
                            "    lt(mptr, mptr_end)",
                            "    {}",
                            "{",
                            "    mstore(mptr, mload(sum_mptr))",
                            "    mptr := add(mptr, 0x20)",
                            "    sum_mptr := add(sum_mptr, 0x20)",
                            "}",
                        ]
                        .map(str::to_string),
                        [
                            format!(
                                "success := batch_invert(success, 0x{batch_invert_2_end:x}, r)"
                            ),
                            format!(
                                "let r_eval := mulmod(mload(0x{:x}), mload(0x{:x}), r)",
                                batch_invert_2_end - 0x20,
                                r_eval_mptr + (rotation_sets.len() - 1) * 0x20
                            )
                        ],
                        ["for", "    {"].map(str::to_string),
                        [
                            format!(
                                "        let sum_inv_mptr := 0x{:x}",
                                batch_invert_2_end - 0x40
                            ),
                            format!("        let sum_inv_mptr_end := 0x{:x}", batch_invert_2_end),
                            format!(
                                "        let r_eval_mptr := 0x{:x}",
                                r_eval_mptr + (rotation_sets.len() - 2) * 0x20
                            ),
                        ],
                        [
                            "    }",
                            "    lt(sum_inv_mptr, sum_inv_mptr_end)",
                            "    {}",
                            "{",
                            "    r_eval := mulmod(r_eval, mload(NU_MPTR), r)",
                            "    r_eval := addmod(r_eval, mulmod(mload(sum_inv_mptr), mload(r_eval_mptr), r), r)",
                            "    sum_inv_mptr := sub(sum_inv_mptr, 0x20)",
                            "    r_eval_mptr := sub(r_eval_mptr, 0x20)",
                            "}",
                            "mstore(R_EVAL_MPTR, r_eval)",
                        ]
                        .map(str::to_string),
                    ]
                    .collect_vec(),
                    chain![
                        rotation_sets
                            .iter()
                            .enumerate()
                            .rev()
                            .flat_map(|(set_idx, set)| {
                                let last_set_idx = rotation_sets.len() - 1;
                                chain![
                                    set.comms()
                                        .last()
                                        .map(|comm| {
                                            if set_idx == last_set_idx {
                                                [
                                                    format!("mstore(0x00, {})", comm.x_asm()),
                                                    format!("mstore(0x20, {})", comm.y_asm()),
                                                ]
                                            } else {
                                                [
                                                    format!("mstore(0x80, {})", comm.x_asm()),
                                                    format!("mstore(0xa0, {})", comm.y_asm()),
                                                ]
                                            }
                                        })
                                        .into_iter()
                                        .flatten(),
                                    set.comms().iter().rev().skip(1).flat_map(move |comm| {
                                        if set_idx == last_set_idx {
                                            [
                                                "success := ec_mul_acc(success, mload(ZETA_MPTR))"
                                                    .to_string(),
                                                format!(
                                                    "success := ec_add_acc(success, {}, {})",
                                                    comm.x_asm(),
                                                    comm.y_asm()
                                                ),
                                            ]
                                        } else {
                                            [
                                                "success := ec_mul_tmp(success, mload(ZETA_MPTR))"
                                                    .to_string(),
                                                format!(
                                                    "success := ec_add_tmp(success, {}, {})",
                                                    comm.x_asm(),
                                                    comm.y_asm()
                                                ),
                                            ]
                                        }
                                    }),
                                    (set_idx != 0).then(|| if set_idx == last_set_idx {
                                        format!(
                                            "success := ec_mul_acc(success, mload({}))",
                                            diff_mptr + set_idx * 0x20
                                        )
                                    } else {
                                        format!(
                                            "success := ec_mul_tmp(success, mload({}))",
                                            diff_mptr + set_idx * 0x20
                                        )
                                    }),
                                    (set_idx != last_set_idx)
                                        .then(|| [
                                            "success := ec_mul_acc(success, mload(NU_MPTR))"
                                                .to_string(),
                                            "success := ec_add_acc(success, mload(0x80), mload(0xa0))".to_string()
                                        ])
                                        .into_iter()
                                        .flatten(),
                                ]
                            }),
                        [
                            "mstore(0x80, mload(G1_X_MPTR))",
                            "mstore(0xa0, mload(G1_Y_MPTR))",
                            "success := ec_mul_tmp(success, sub(r, mload(R_EVAL_MPTR)))",
                            "success := ec_add_acc(success, mload(0x80), mload(0xa0))",
                        ]
                        .map(str::to_string),
                        [
                            format!("mstore(0x80, calldataload(0x{:x}))", w_cptr),
                            format!("mstore(0xa0, calldataload(0x{:x}))", w_cptr + 0x20),
                            format!("success := ec_mul_tmp(success, sub(r, mload(0x{vanishing_mptr:x})))"),
                        ],
                        ["success := ec_add_acc(success, mload(0x80), mload(0xa0))".to_string()],
                        [
                            format!("mstore(0x80, calldataload(0x{:x}))", w_prime_cptr),
                            format!("mstore(0xa0, calldataload(0x{:x}))", w_prime_cptr + 0x20),
                        ],
                        [
                            "success := ec_mul_tmp(success, mload(MU_MPTR))",
                            "success := ec_add_acc(success, mload(0x80), mload(0xa0))",
                            "mstore(PAIRING_LHS_X_MPTR, mload(0x00))",
                            "mstore(PAIRING_LHS_Y_MPTR, mload(0x20))",
                        ]
                        .map(str::to_string),
                        [
                            format!(
                                "mstore(PAIRING_RHS_X_MPTR, calldataload(0x{:x}))",
                                w_prime_cptr
                            ),
                            format!(
                                "mstore(PAIRING_RHS_Y_MPTR, calldataload(0x{:x}))",
                                w_prime_cptr + 0x20
                            ),
                        ],
                    ]
                    .collect_vec()
                ],
            ]
            .collect_vec()
        };

        let vk = Halo2VerifyingKey { chunks: vk_chunks };
        let verifier = Halo2Verifier {
            vk_mptr,
            vk_len,
            num_neg_lagranges,
            num_witnesses,
            num_challenges,
            num_evals,
            num_quotients,
            quotient_cptr,
            proof_len,
            challenge_mptr,
            theta_mptr,
            instance_eval_mptr,
            expression_computations,
            pcs_computations,
        };

        (vk, verifier)
    }
}

fn calldataload_asm(cptr: usize) -> String {
    format!("calldataload(0x{cptr:x})")
}

fn mload_asm(mptr: usize) -> String {
    format!("mload(0x{mptr:x})")
}
