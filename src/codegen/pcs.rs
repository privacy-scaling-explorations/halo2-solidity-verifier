#![allow(clippy::useless_format)]

use crate::codegen::util::{ptr, ConstraintSystemMeta, Data, EcPoint, Ptr, U256Expr};
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
            let comm = data.advice_comms[query.0];
            let eval = data.advice_evals[query];
            Query::new(comm, query.1, eval)
        }),
        izip!(&data.permutation_z_comms, &data.permutation_z_evals).flat_map(|(&comm, evals)| {
            [Query::new(comm, 0, evals.0), Query::new(comm, 1, evals.1)]
        }),
        izip!(&data.permutation_z_comms, &data.permutation_z_evals)
            .rev()
            .skip(1)
            .map(|(&comm, evals)| Query::new(comm, meta.rotation_last, evals.2)),
        izip!(
            &data.lookup_permuted_comms,
            &data.lookup_z_comms,
            &data.lookup_evals
        )
        .flat_map(|(permuted_comms, &z_comm, evals)| {
            [
                Query::new(z_comm, 0, evals.0),
                Query::new(permuted_comms.0, 0, evals.2),
                Query::new(permuted_comms.1, 0, evals.4),
                Query::new(permuted_comms.0, -1, evals.3),
                Query::new(z_comm, 1, evals.1),
            ]
        }),
        meta.fixed_queries.iter().map(|query| {
            let comm = data.fixed_comms[query.0];
            let eval = data.fixed_evals[query];
            Query::new(comm, query.1, eval)
        }),
        meta.permutation_columns.iter().map(|column| {
            let comm = data.permutation_comms[column];
            let eval = data.permutation_evals[column];
            Query::new(comm, 0, eval)
        }),
        [
            Query::new(data.quotient_comm, 0, data.quotient_eval),
            Query::new(data.random_comm, 0, data.random_eval),
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
                    query.comm,
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
    let w_prime = w + 1;

    let diff_0_mptr = ptr!();
    let coeff_mptrs = sets
        .iter()
        .scan(diff_0_mptr + 1, |state, set| {
            let ptrs = state.range_from().take(set.rots().len()).collect_vec();
            *state = *state + set.rots().len();
            Some(ptrs)
        })
        .collect_vec();

    let num_coeffs = sets.iter().map(|set| set.rots().len()).sum::<usize>();
    let first_batch_invert_end = ptr!(1 + num_coeffs);
    let second_batch_invert_end = ptr!(sets.len());
    let free_mptr = ptr!(2 * (1 + num_coeffs) + 6);

    let min_rot = *superset.first().unwrap();
    let max_rot = *superset.last().unwrap();
    let point_vars = superset
        .iter()
        .zip((0..).map(|idx| format!("point_{idx}")))
        .collect::<BTreeMap<_, _>>();
    let point_mptrs = superset
        .iter()
        .zip(free_mptr.range_from())
        .collect::<BTreeMap<_, _>>();
    let mu_minus_point_mptrs = superset
        .iter()
        .zip((free_mptr + superset.len()).range_from())
        .collect::<BTreeMap<_, _>>();

    let vanishing_mptr = free_mptr + superset.len() * 2;
    let diff_mptr = vanishing_mptr + 1;
    let r_eval_mptr = diff_mptr + sets.len();
    let sum_mptr = r_eval_mptr + sets.len();

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
                point_mptrs
                    .get(&rot)
                    .map(|mptr| format!("mstore({mptr}, x_pow_of_omega)")),
                (rot != max_rot)
                    .then(|| { "x_pow_of_omega := mulmod(x_pow_of_omega, omega, r)".to_string() })
            ]
        }),
        [
            format!("mstore({}, x)", point_mptrs[&0]),
            format!("x_pow_of_omega := mulmod(x, omega_inv, r)")
        ],
        (min_rot..0).rev().flat_map(|rot| {
            chain![
                point_mptrs
                    .get(&rot)
                    .map(|mptr| format!("mstore({mptr}, x_pow_of_omega)")),
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
                "        let mptr := {}",
                mu_minus_point_mptrs.first_key_value().unwrap().1
            ),
            format!(
                "        let mptr_end := {}",
                *mu_minus_point_mptrs.first_key_value().unwrap().1 + mu_minus_point_mptrs.len()
            ),
            format!("        let point_mptr := {free_mptr}"),
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
                "s := mload({})",
                mu_minus_point_mptrs[sets[0].rots().first().unwrap()]
            )],
            sets[0].rots().iter().skip(1).map(|rot| {
                let item = format!("mload({})", mu_minus_point_mptrs[rot]);
                format!("s := mulmod(s, {item}, r)")
            }),
            [format!("mstore({}, s)", vanishing_mptr)],
        ],
        ["let diff".to_string()],
        sets.iter()
            .zip(diff_mptr.range_from())
            .flat_map(|(set, mptr)| {
                chain![
                    [format!(
                        "diff := mload({})",
                        mu_minus_point_mptrs[set.diffs().first().unwrap()]
                    )],
                    set.diffs().iter().skip(1).map(|rot| {
                        let item = format!("mload({})", mu_minus_point_mptrs[rot]);
                        format!("diff := mulmod(diff, {item}, r)")
                    }),
                    [format!("mstore({}, diff)", mptr)],
                    (mptr == diff_mptr).then(|| format!("mstore({diff_0_mptr}, diff)")),
                ]
            })
    ]
    .collect_vec();

    let coeff_computations = izip!(&sets, &coeff_mptrs)
        .map(|(set, coeff_mptrs)| {
            let coeff_points = set
                .rots()
                .iter()
                .map(|rot| &point_vars[rot])
                .enumerate()
                .map(|(i, rot_i)| {
                    set.rots()
                        .iter()
                        .map(|rot| &point_vars[rot])
                        .enumerate()
                        .filter_map(|(j, rot_j)| (i != j).then_some((rot_i, rot_j)))
                        .collect_vec()
                })
                .collect_vec();
            chain![
                set.rots().iter().map(|rot| {
                    format!("let {} := mload({})", &point_vars[rot], point_mptrs[rot])
                }),
                ["let coeff".to_string()],
                izip!(set.rots(), &coeff_points, coeff_mptrs).flat_map(
                    |(rot_i, coeff_points, coeff_mptr)| chain![
                        [coeff_points
                            .first()
                            .map(|(point_i, point_j)| {
                                format!("coeff := addmod({point_i}, sub(r, {point_j}), r)")
                            })
                            .unwrap_or_else(|| { "coeff := 1".to_string() })],
                        coeff_points.iter().skip(1).map(|(point_i, point_j)| {
                            let item = format!("addmod({point_i}, sub(r, {point_j}), r)",);
                            format!("coeff := mulmod(coeff, {item}, r)")
                        }),
                        [
                            format!(
                                "coeff := mulmod(coeff, mload({}), r)",
                                mu_minus_point_mptrs[rot_i]
                            ),
                            format!("mstore({coeff_mptr}, coeff)")
                        ],
                    ]
                )
            ]
            .collect_vec()
        })
        .collect_vec();

    let normalized_coeff_computations = chain![
        [
            format!("success := batch_invert(success, {first_batch_invert_end}, r)"),
            format!("let diff_0_inv := mload({diff_0_mptr})"),
            format!("mstore({diff_mptr}, diff_0_inv)"),
        ],
        ["for", "    {"].map(str::to_string),
        [
            format!("        let mptr := {}", diff_mptr + 1),
            format!("        let mptr_end := {}", diff_mptr + sets.len()),
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

    let r_evals_computations = izip!(0.., &sets, &coeff_mptrs, r_eval_mptr.range_from()).map(
        |(idx, set, coeff_mptrs, r_eval_mptr)| {
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
                            izip!(evals, coeff_mptrs).map(|(eval, coeff_mptr)| {
                                let item = format!("mulmod(mload({coeff_mptr}), {eval}, r)");
                                format!("r_eval := addmod(r_eval, {item}, r)")
                            }),
                            (idx != 0).then(|| "r_eval := mulmod(r_eval, zeta, r)".to_string()),
                        ]
                    }),
                (idx != 0)
                    .then(|| format!("r_eval := mulmod(r_eval, mload({}), r)", diff_mptr + idx)),
                [format!("mstore({r_eval_mptr}, r_eval)")],
            ]
            .collect_vec()
        },
    );

    let coeff_sums_computation =
        izip!(&coeff_mptrs, sum_mptr.range_from()).map(|(coeff_mptrs, sum_mptr)| {
            let (coeff_0_mptr, rest_coeff_mptrs) = coeff_mptrs.split_first().unwrap();
            chain![
                [format!("let sum := mload({coeff_0_mptr})")],
                rest_coeff_mptrs
                    .iter()
                    .map(|coeff_mptr| format!("sum := addmod(sum, mload({coeff_mptr}), r)")),
                [format!("mstore({sum_mptr}, sum)")],
            ]
            .collect_vec()
        });

    let r_eval_computations =
        chain![
        ["for", "    {", "        let mptr := 0x00"].map(str::to_string),
        [
            format!("        let mptr_end := {}", second_batch_invert_end),
            format!("        let sum_mptr := {}", sum_mptr),
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
            format!("success := batch_invert(success, {second_batch_invert_end}, r)"),
            format!(
                "let r_eval := mulmod(mload({}), mload({}), r)",
                second_batch_invert_end - 1,
                r_eval_mptr + sets.len() - 1
            )
        ],
        ["for", "    {"].map(str::to_string),
        [
            format!(
                "        let sum_inv_mptr := {}",
                second_batch_invert_end - 2
            ),
            format!("        let sum_inv_mptr_end := {}", second_batch_invert_end),
            format!(
                "        let r_eval_mptr := {}",
                r_eval_mptr + sets.len() - 2
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
                        diff_mptr + set_idx
                    )
                } else {
                    format!(
                        "success := ec_mul_tmp(success, mload({}))",
                        diff_mptr + set_idx
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
            format!("success := ec_mul_tmp(success, sub(r, mload({vanishing_mptr})))"),
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
