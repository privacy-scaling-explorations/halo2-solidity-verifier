#![allow(clippy::useless_format)]

use crate::codegen::util::{ConstraintSystemMeta, Data, EcPoint, U256Expr};
use itertools::{chain, izip, Itertools};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BatchOpenScheme {
    Gwc19,
    Bdfg21,
}

#[derive(Debug)]
pub struct Query {
    comm: EcPoint,
    rot: i32,
    eval: U256Expr,
}

impl Query {
    fn new(comm: EcPoint, rot: i32, eval: U256Expr) -> Self {
        Self { comm, rot, eval }
    }
}

pub(crate) fn queries(meta: &ConstraintSystemMeta, data: &Data) -> Vec<Query> {
    chain![
        meta.advice_queries.iter().map(|query| {
            let comm = data.advice_comms[query.0].clone();
            let eval = data.advice_evals[query].clone();
            Query::new(comm, query.1, eval)
        }),
        izip!(&data.permutation_z_comms, &data.permutation_z_evals).flat_map(|(comm, evals)| {
            [
                Query::new(comm.clone(), 0, evals.0.clone()),
                Query::new(comm.clone(), 1, evals.1.clone()),
            ]
        }),
        izip!(&data.permutation_z_comms, &data.permutation_z_evals)
            .rev()
            .skip(1)
            .map(|(comm, evals)| Query::new(comm.clone(), meta.rotation_last, evals.2.clone())),
        izip!(
            &data.lookup_permuted_comms,
            &data.lookup_z_comms,
            &data.lookup_evals
        )
        .flat_map(|(permuted_comms, z_comm, evals)| {
            [
                Query::new(z_comm.clone(), 0, evals.0.clone()),
                Query::new(permuted_comms.0.clone(), 0, evals.2.clone()),
                Query::new(permuted_comms.1.clone(), 0, evals.4.clone()),
                Query::new(permuted_comms.0.clone(), -1, evals.3.clone()),
                Query::new(z_comm.clone(), 1, evals.1.clone()),
            ]
        }),
        meta.fixed_queries.iter().map(|query| {
            let comm = data.fixed_comms[query.0].clone();
            let eval = data.fixed_evals[query].clone();
            Query::new(comm, query.1, eval)
        }),
        meta.permutation_columns.iter().map(|column| {
            let comm = data.permutation_comms[column].clone();
            let eval = data.permutation_evals[column].clone();
            Query::new(comm, 0, eval)
        }),
        [
            Query::new(data.quotient_comm.clone(), 0, data.quotient_eval.clone()),
            Query::new(data.random_comm.clone(), 0, data.random_eval.clone()),
        ]
    ]
    .collect()
}

#[derive(Debug)]
pub struct RotationSet {
    rots: BTreeSet<i32>,
    diffs: BTreeSet<i32>,
    comms: Vec<EcPoint>,
    evals: Vec<Vec<String>>,
}

impl RotationSet {
    pub fn rots(&self) -> &BTreeSet<i32> {
        &self.rots
    }

    pub fn diffs(&self) -> &BTreeSet<i32> {
        &self.diffs
    }

    pub fn comms(&self) -> &[EcPoint] {
        &self.comms
    }

    pub fn evals(&self) -> &[Vec<String>] {
        &self.evals
    }
}

pub fn rotation_sets(queries: &[Query]) -> (BTreeSet<i32>, Vec<RotationSet>) {
    let mut superset = BTreeSet::new();
    let comm_queries = queries.iter().fold(
        Vec::<(EcPoint, BTreeMap<i32, String>)>::new(),
        |mut comm_queries, query| {
            superset.insert(query.rot);
            if let Some(pos) = comm_queries
                .iter()
                .position(|(comm, _)| comm == &query.comm)
            {
                let (_, queries) = &mut comm_queries[pos];
                assert!(!queries.contains_key(&query.rot));
                queries.insert(query.rot, query.eval.to_string());
            } else {
                comm_queries.push((
                    query.comm.clone(),
                    BTreeMap::from_iter([(query.rot, query.eval.to_string())]),
                ));
            }
            comm_queries
        },
    );
    let superset = superset;
    let sets =
        comm_queries
            .into_iter()
            .fold(Vec::<RotationSet>::new(), |mut sets, (comm, queries)| {
                if let Some(pos) = sets
                    .iter()
                    .position(|set| itertools::equal(&set.rots, queries.keys()))
                {
                    let set = &mut sets[pos];
                    if !set.comms.contains(&comm) {
                        set.comms.push(comm);
                        set.evals.push(queries.into_values().collect_vec());
                    }
                } else {
                    let diffs = BTreeSet::from_iter(
                        superset
                            .iter()
                            .filter(|rot| !queries.contains_key(rot))
                            .copied(),
                    );
                    let set = RotationSet {
                        rots: BTreeSet::from_iter(queries.keys().copied()),
                        diffs,
                        comms: vec![comm],
                        evals: vec![queries.into_values().collect()],
                    };
                    sets.push(set);
                }
                sets
            });
    (superset, sets)
}

pub(crate) fn shplonk_computations(meta: &ConstraintSystemMeta, data: &Data) -> Vec<Vec<String>> {
    let queries = queries(meta, data);
    let (superset, sets) = rotation_sets(&queries);

    let w = EcPoint::cptr(data.w_cptr);
    let w_prime = EcPoint::cptr(data.w_cptr + 0x40);

    let diff_0_mptr = 0x00;
    let coeff_mptr = sets
        .iter()
        .scan(diff_0_mptr + 0x20, |state, set| {
            let mptr = *state;
            *state += set.rots().len() * 0x20;
            Some(mptr)
        })
        .collect_vec();

    let num_coeffs = sets.iter().map(|set| set.rots().len()).sum::<usize>();
    let batch_invert_1_end = (1 + num_coeffs) * 0x20;
    let batch_invert_2_end = sets.len() * 0x20;
    let free_mptr = batch_invert_1_end * 2 + 6 * 0x20;

    let min_rot = *superset.first().unwrap();
    let max_rot = *superset.last().unwrap();
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
    let r_eval_mptr = diff_mptr + sets.len() * 0x20;
    let sum_mptr = r_eval_mptr + sets.len() * 0x20;

    let point_computations = chain![
        [
            "let x := mload(X_MPTR)",
            "let omega := mload(OMEGA_MPTR)",
            "let omega_inv := mload(OMEGA_INV_MPTR)",
            "let x_pow_of_omega := mulmod(x, omega, r)"
        ]
        .map(str::to_string),
        (1..=max_rot).flat_map(|rot| {
            chain![
                point_mptr
                    .get(&rot)
                    .map(|mptr| format!("mstore(0x{mptr:x}, x_pow_of_omega)",)),
                (rot != max_rot)
                    .then(|| { "x_pow_of_omega := mulmod(x_pow_of_omega, omega, r)".to_string() })
            ]
        }),
        [
            format!("mstore(0x{:x}, x)", point_mptr[&0]),
            "x_pow_of_omega := mulmod(x, omega_inv, r)".to_string()
        ],
        (min_rot..0).rev().flat_map(|rot| {
            chain![
                point_mptr
                    .get(&rot)
                    .map(|mptr| format!("mstore(0x{mptr:x}, x_pow_of_omega)",)),
                (rot != min_rot).then(|| {
                    "x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)".to_string()
                })
            ]
        })
    ]
    .collect_vec();

    let vanishing_computations = chain![
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
                mu_minus_point_mptr[sets[0].rots().first().unwrap()]
            )],
            sets[0].rots().iter().skip(1).map(|rot| {
                let item = format!("mload(0x{:x})", mu_minus_point_mptr[rot]);
                format!("s := mulmod(s, {item}, r)")
            }),
            [format!("mstore(0x{:x}, s)", vanishing_mptr)],
        ],
        ["let diff".to_string()],
        sets.iter()
            .zip((diff_mptr..).step_by(0x20))
            .flat_map(|(set, mptr)| {
                chain![
                    [format!(
                        "diff := mload(0x{:x})",
                        mu_minus_point_mptr[set.diffs().first().unwrap()]
                    )],
                    set.diffs().iter().skip(1).map(|rot| {
                        let item = format!("mload(0x{:x})", mu_minus_point_mptr[rot]);
                        format!("diff := mulmod(diff, {item}, r)")
                    }),
                    [format!("mstore(0x{:x}, diff)", mptr)],
                    (mptr == diff_mptr).then(|| format!("mstore(0x{diff_0_mptr:x}, diff)")),
                ]
            })
    ]
    .collect_vec();

    let coeff_computations = sets
        .iter()
        .enumerate()
        .map(|(idx, set)| {
            let coeff_rotations = set
                .rots()
                .iter()
                .enumerate()
                .map(|(i, rotation_i)| {
                    set.rots()
                        .iter()
                        .enumerate()
                        .filter_map(move |(j, rotation_j)| {
                            (i != j).then_some((rotation_i, rotation_j))
                        })
                        .collect_vec()
                })
                .collect_vec();
            chain![
                set.rots().iter().map(|rot| {
                    format!(
                        "let point_{} := mload(0x{:x})",
                        point_idx[rot], point_mptr[rot]
                    )
                }),
                ["let coeff".to_string()],
                izip!(
                    set.rots(),
                    &coeff_rotations,
                    (coeff_mptr[idx]..).step_by(0x20)
                )
                .flat_map(|(rotation_i, rots, mptr)| chain![
                    [rots
                        .first()
                        .map(|rot| {
                            format!(
                                "coeff := addmod(point_{}, sub(r, point_{}), r)",
                                point_idx[&rot.0], point_idx[&rot.1]
                            )
                        })
                        .unwrap_or_else(|| { "coeff := 1".to_string() })],
                    rots.iter().skip(1).map(|(i, j)| {
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
                ])
            ]
            .collect_vec()
        })
        .collect_vec();

    let normalized_coeff_computations = chain![
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
                diff_mptr + sets.len() * 0x20
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
    .collect_vec();

    let r_evals_computations = izip!(0.., &sets, &coeff_mptr, (r_eval_mptr..).step_by(0x20)).map(
        |(idx, set, coeff_mptr, r_eval_mptr)| {
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
                                    let item =
                                        format!("mulmod(mload(0x{coeff_mptr:x}), {eval}, r)");
                                    format!("r_eval := addmod(r_eval, {item}, r)")
                                }
                            ),
                            (idx != 0).then(|| "r_eval := mulmod(r_eval, zeta, r)".to_string()),
                        ]
                    }),
                (idx != 0).then(|| format!(
                    "r_eval := mulmod(r_eval, mload(0x{:x}), r)",
                    diff_mptr + idx * 0x20
                )),
                [format!("mstore(0x{r_eval_mptr:x}, r_eval)")],
            ]
            .collect_vec()
        },
    );

    let coeff_sums_computation =
        izip!(&sets, &coeff_mptr, (sum_mptr..).step_by(0x20)).map(|(set, coeff_mptr, sum_mptr)| {
            chain![
                [format!("let sum := mload(0x{coeff_mptr:x})")],
                (*coeff_mptr..)
                    .step_by(0x20)
                    .take(set.rots().len())
                    .skip(1)
                    .map(|coeff_mptr| format!("sum := addmod(sum, mload(0x{coeff_mptr:x}), r)")),
                [format!("mstore(0x{sum_mptr:x}, sum)")],
            ]
            .collect_vec()
        });

    let r_eval_computations = chain![
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
            format!("success := batch_invert(success, 0x{batch_invert_2_end:x}, r)"),
            format!(
                "let r_eval := mulmod(mload(0x{:x}), mload(0x{:x}), r)",
                batch_invert_2_end - 0x20,
                r_eval_mptr + (sets.len() - 1) * 0x20
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
                r_eval_mptr + (sets.len() - 2) * 0x20
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
    .collect_vec();

    let pairing_input_computations = chain![
        sets.iter().enumerate().rev().flat_map(|(set_idx, set)| {
            let last_set_idx = sets.len() - 1;
            chain![
                set.comms()
                    .last()
                    .map(|comm| {
                        if set_idx == last_set_idx {
                            [
                                format!("mstore(0x00, {})", comm.x()),
                                format!("mstore(0x20, {})", comm.y()),
                            ]
                        } else {
                            [
                                format!("mstore(0x80, {})", comm.x()),
                                format!("mstore(0xa0, {})", comm.y()),
                            ]
                        }
                    })
                    .into_iter()
                    .flatten(),
                set.comms().iter().rev().skip(1).flat_map(move |comm| {
                    if set_idx == last_set_idx {
                        [
                            "success := ec_mul_acc(success, mload(ZETA_MPTR))".to_string(),
                            format!("success := ec_add_acc(success, {}, {})", comm.x(), comm.y()),
                        ]
                    } else {
                        [
                            "success := ec_mul_tmp(success, mload(ZETA_MPTR))".to_string(),
                            format!("success := ec_add_tmp(success, {}, {})", comm.x(), comm.y()),
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
                        "success := ec_mul_acc(success, mload(NU_MPTR))".to_string(),
                        "success := ec_add_acc(success, mload(0x80), mload(0xa0))".to_string()
                    ])
                    .into_iter()
                    .flatten(),
            ]
        }),
        [
            format!("mstore(0x80, mload(G1_X_MPTR))"),
            format!("mstore(0xa0, mload(G1_Y_MPTR))"),
            format!("success := ec_mul_tmp(success, sub(r, mload(R_EVAL_MPTR)))"),
            format!("success := ec_add_acc(success, mload(0x80), mload(0xa0))"),
            format!("mstore(0x80, {})", w.x()),
            format!("mstore(0xa0, {})", w.y()),
            format!("success := ec_mul_tmp(success, sub(r, mload(0x{vanishing_mptr:x})))"),
            format!("success := ec_add_acc(success, mload(0x80), mload(0xa0))"),
            format!("mstore(0x80, {})", w_prime.x()),
            format!("mstore(0xa0, {})", w_prime.y()),
            format!("success := ec_mul_tmp(success, mload(MU_MPTR))"),
            format!("success := ec_add_acc(success, mload(0x80), mload(0xa0))"),
            format!("mstore(PAIRING_LHS_X_MPTR, mload(0x00))"),
            format!("mstore(PAIRING_LHS_Y_MPTR, mload(0x20))"),
            format!("mstore(PAIRING_RHS_X_MPTR, {})", w_prime.x()),
            format!("mstore(PAIRING_RHS_Y_MPTR, {})", w_prime.y()),
        ],
    ]
    .collect_vec();

    chain![
        [point_computations, vanishing_computations],
        coeff_computations,
        [normalized_coeff_computations],
        r_evals_computations,
        coeff_sums_computation,
        [r_eval_computations, pairing_input_computations],
    ]
    .collect_vec()
}
