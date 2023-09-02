#![allow(clippy::useless_format)]

use crate::codegen::util::{
    for_loop, ptr, ConstraintSystemMeta, Data, EcPoint, Location, Ptr, U256Expr,
};
use itertools::{chain, izip, Itertools};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BatchOpenScheme {
    Gwc19,
    Bdfg21,
}

#[derive(Debug)]
pub(crate) struct Query {
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
            Query::new(data.computed_quotient_comm, 0, data.computed_quotient_eval),
            Query::new(data.random_comm, 0, data.random_eval),
        ]
    ]
    .collect()
}

#[derive(Debug)]
pub(crate) struct RotationSet {
    rots: BTreeSet<i32>,
    diffs: BTreeSet<i32>,
    comms: Vec<EcPoint>,
    evals: Vec<Vec<U256Expr>>,
}

impl RotationSet {
    pub(crate) fn rots(&self) -> &BTreeSet<i32> {
        &self.rots
    }

    pub(crate) fn diffs(&self) -> &BTreeSet<i32> {
        &self.diffs
    }

    pub(crate) fn comms(&self) -> &[EcPoint] {
        &self.comms
    }

    pub(crate) fn evals(&self) -> &[Vec<U256Expr>] {
        &self.evals
    }
}

pub(crate) fn rotation_sets(queries: &[Query]) -> (BTreeSet<i32>, Vec<RotationSet>) {
    let mut superset = BTreeSet::new();
    let comm_queries = queries.iter().fold(
        Vec::<(EcPoint, BTreeMap<i32, U256Expr>)>::new(),
        |mut comm_queries, query| {
            superset.insert(query.rot);
            if let Some(pos) = comm_queries
                .iter()
                .position(|(comm, _)| comm == &query.comm)
            {
                let (_, queries) = &mut comm_queries[pos];
                assert!(!queries.contains_key(&query.rot));
                queries.insert(query.rot, query.eval);
            } else {
                comm_queries.push((query.comm, BTreeMap::from_iter([(query.rot, query.eval)])));
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

pub(crate) fn bdfg21_computations(meta: &ConstraintSystemMeta, data: &Data) -> Vec<Vec<String>> {
    let queries = queries(meta, data);
    let (superset, sets) = rotation_sets(&queries);

    let w = EcPoint::cptr(data.w_cptr);
    let w_prime = w + 1;

    let diff_0_mptr = ptr!();
    let coeff_mptrs = sets
        .iter()
        .scan(diff_0_mptr + 1, |state, set| {
            let ptrs = Ptr::range_from(*state).take(set.rots().len()).collect_vec();
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
        .zip(Ptr::range_from(free_mptr))
        .collect::<BTreeMap<_, _>>();
    let mu_minus_point_mptrs = superset
        .iter()
        .zip(Ptr::range_from(free_mptr + superset.len()))
        .collect::<BTreeMap<_, _>>();

    let vanishing_0_mptr = free_mptr + 2 * superset.len();
    let diff_mptr = vanishing_0_mptr + 1;
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
        ["let mu := mload(MU_MPTR)".to_string()],
        {
            let mptr = *mu_minus_point_mptrs.first_key_value().unwrap().1;
            let mptr_end = mptr + mu_minus_point_mptrs.len();
            for_loop(
                [
                    format!("let mptr := {mptr}"),
                    format!("let mptr_end := {mptr_end}"),
                    format!("let point_mptr := {free_mptr}"),
                ],
                "lt(mptr, mptr_end)",
                [
                    "mptr := add(mptr, 0x20)",
                    "point_mptr := add(point_mptr, 0x20)",
                ]
                .map(str::to_string),
                ["mstore(mptr, addmod(mu, sub(r, mload(point_mptr)), r))".to_string()],
            )
        },
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
            [format!("mstore({}, s)", vanishing_0_mptr)],
        ],
        ["let diff".to_string()],
        izip!(&sets, Ptr::range_from(diff_mptr)).flat_map(|(set, mptr)| {
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
                            let item = format!("addmod({point_i}, sub(r, {point_j}), r)");
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
        for_loop(
            [
                format!("let mptr := {}", diff_mptr + 1),
                format!("let mptr_end := {}", diff_mptr + sets.len()),
            ],
            "lt(mptr, mptr_end)",
            ["mptr := add(mptr, 0x20)".to_string()],
            ["mstore(mptr, mulmod(mload(mptr), diff_0_inv, r))".to_string()],
        ),
    ]
    .collect_vec();

    let r_evals_computations = izip!(
        0..,
        &sets,
        &coeff_mptrs,
        Ptr::range_from(diff_mptr),
        Ptr::range_from(r_eval_mptr),
    )
    .map(|(set_idx, set, coeff_mptrs, set_coeff_mptr, r_eval_mptr)| {
        let is_single_rot_set = set.rots().len() == 1;
        chain![
            is_single_rot_set.then(|| format!("let coeff := mload({})", coeff_mptrs[0])),
            ["let zeta := mload(ZETA_MPTR)", "let r_eval := 0"].map(str::to_string),
            if is_single_rot_set {
                let eval_groups = set.evals().iter().rev().fold(
                    Vec::<Vec<&U256Expr>>::new(),
                    |mut eval_groups, evals| {
                        let eval = &evals[0];
                        if let Some(last_group) = eval_groups.last_mut() {
                            let last_eval = **last_group.last().unwrap();
                            if last_eval.ptr().is_integer() && last_eval - 1 == *eval {
                                last_group.push(eval)
                            } else {
                                eval_groups.push(vec![eval])
                            }
                            eval_groups
                        } else {
                            vec![vec![eval]]
                        }
                    },
                );
                chain![eval_groups.iter().enumerate()]
                    .flat_map(|(group_idx, evals)| {
                        if evals.len() < 3 {
                            chain![evals.iter().enumerate()]
                                .flat_map(|(eval_idx, eval)| {
                                    let is_first_eval = group_idx == 0 && eval_idx == 0;
                                    let item = format!("mulmod(coeff, {eval}, r)");
                                    chain![
                                        (!is_first_eval)
                                            .then(|| format!("r_eval := mulmod(r_eval, zeta, r)")),
                                        [format!("r_eval := addmod(r_eval, {item}, r)")],
                                    ]
                                })
                                .collect_vec()
                        } else {
                            let item = "mulmod(coeff, calldataload(mptr), r)";
                            for_loop(
                                [
                                    format!("let mptr := {}", evals[0].ptr()),
                                    format!("let mptr_end := {}", evals[0].ptr() - evals.len()),
                                ],
                                "lt(mptr_end, mptr)".to_string(),
                                ["mptr := sub(mptr, 0x20)".to_string()],
                                [format!(
                                    "r_eval := addmod(mulmod(r_eval, zeta, r), {item}, r)"
                                )],
                            )
                        }
                    })
                    .collect_vec()
            } else {
                chain![set.evals().iter().enumerate().rev()]
                    .flat_map(|(idx, evals)| {
                        chain![
                            izip!(evals, coeff_mptrs).map(|(eval, coeff_mptr)| {
                                let item = format!("mulmod(mload({coeff_mptr}), {eval}, r)");
                                format!("r_eval := addmod(r_eval, {item}, r)")
                            }),
                            (idx != 0).then(|| format!("r_eval := mulmod(r_eval, zeta, r)")),
                        ]
                    })
                    .collect_vec()
            },
            (set_idx != 0).then(|| format!("r_eval := mulmod(r_eval, mload({set_coeff_mptr}), r)")),
            [format!("mstore({r_eval_mptr}, r_eval)")],
        ]
        .collect_vec()
    });

    let coeff_sums_computation =
        izip!(&coeff_mptrs, Ptr::range_from(sum_mptr)).map(|(coeff_mptrs, sum_mptr)| {
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

    let r_eval_computations = chain![
        for_loop(
            [
                format!("let mptr := 0x00"),
                format!("let mptr_end := {}", second_batch_invert_end),
                format!("let sum_mptr := {}", sum_mptr),
            ],
            "lt(mptr, mptr_end)",
            ["mptr := add(mptr, 0x20)", "sum_mptr := add(sum_mptr, 0x20)"].map(str::to_string),
            ["mstore(mptr, mload(sum_mptr))".to_string()],
        ),
        [
            format!("success := batch_invert(success, {second_batch_invert_end}, r)"),
            format!(
                "let r_eval := mulmod(mload({}), mload({}), r)",
                second_batch_invert_end - 1,
                r_eval_mptr + sets.len() - 1
            )
        ],
        for_loop(
            [
                format!("let sum_inv_mptr := {}", second_batch_invert_end - 2),
                format!("let sum_inv_mptr_end := {}", second_batch_invert_end),
                format!("let r_eval_mptr := {}", r_eval_mptr + sets.len() - 2),
            ],
            "lt(sum_inv_mptr, sum_inv_mptr_end)",
            [
                "sum_inv_mptr := sub(sum_inv_mptr, 0x20)",
                "r_eval_mptr := sub(r_eval_mptr, 0x20)"
            ]
            .map(str::to_string),
            [
                "r_eval := mulmod(r_eval, mload(NU_MPTR), r)",
                "r_eval := addmod(r_eval, mulmod(mload(sum_inv_mptr), mload(r_eval_mptr), r), r)"
            ]
            .map(str::to_string),
        ),
        ["mstore(R_EVAL_MPTR, r_eval)".to_string()],
    ]
    .collect_vec();

    let pairing_input_computations = chain![
        ["let nu := mload(NU_MPTR)".to_string()],
        sets.iter().enumerate().flat_map(|(set_idx, set)| {
            let is_first_set = set_idx == 0;
            let is_last_set = set_idx == sets.len() - 1;
            let set_coeff_mptr = diff_mptr + set_idx;

            let ec_add = &format!("ec_add_{}", if is_first_set { "acc" } else { "tmp" });
            let ec_mul = &format!("ec_mul_{}", if is_first_set { "acc" } else { "tmp" });
            let acc_x = if is_first_set { ptr!() } else { ptr!(4) };
            let acc_y = acc_x + 1;

            let comm_groups = set.comms().iter().rev().skip(1).fold(
                Vec::<(Location, Vec<&EcPoint>)>::new(),
                |mut comm_groups, comm| {
                    if let Some(last_group) = comm_groups.last_mut() {
                        let last_comm = **last_group.1.last().unwrap();
                        if last_group.0 == comm.loc()
                            && last_comm.x().ptr().is_integer()
                            && last_comm - 1 == *comm
                        {
                            last_group.1.push(comm)
                        } else {
                            comm_groups.push((comm.loc(), vec![comm]))
                        }
                        comm_groups
                    } else {
                        vec![(comm.loc(), vec![comm])]
                    }
                },
            );

            chain![
                set.comms()
                    .last()
                    .map(|comm| {
                        [
                            format!("mstore({acc_x}, {})", comm.x()),
                            format!("mstore({acc_y}, {})", comm.y()),
                        ]
                    })
                    .into_iter()
                    .flatten(),
                comm_groups.iter().flat_map(move |(loc, comms)| {
                    if comms.len() < 3 {
                        comms
                            .iter()
                            .flat_map(|comm| {
                                let (x, y) = (comm.x(), comm.y());
                                [
                                    format!("success := {ec_mul}(success, mload(ZETA_MPTR))"),
                                    format!("success := {ec_add}(success, {x}, {y})"),
                                ]
                            })
                            .collect_vec()
                    } else {
                        let mptr = comms.first().unwrap().x().ptr();
                        let mptr_end = mptr - 2 * comms.len();
                        let x = format!("{loc}(mptr)");
                        let y = format!("{loc}(add(mptr, 0x20))");
                        for_loop(
                            [
                                format!("let mptr := {mptr}"),
                                format!("let mptr_end := {mptr_end}"),
                            ],
                            "lt(mptr_end, mptr)",
                            ["mptr := sub(mptr, 0x40)".to_string()],
                            [
                                format!("success := {ec_mul}(success, mload(ZETA_MPTR))"),
                                format!("success := {ec_add}(success, {x}, {y})"),
                            ],
                        )
                    }
                }),
                (!is_first_set)
                    .then(|| {
                        let scalar = format!("mulmod(nu, mload({set_coeff_mptr}), r)");
                        chain![
                            [
                                format!("success := ec_mul_tmp(success, {scalar})"),
                                format!("success := ec_add_acc(success, mload(0x80), mload(0xa0))"),
                            ],
                            (!is_last_set).then(|| format!("nu := mulmod(nu, mload(NU_MPTR), r)"))
                        ]
                    })
                    .into_iter()
                    .flatten(),
            ]
            .collect_vec()
        }),
        [
            format!("mstore(0x80, mload(G1_X_MPTR))"),
            format!("mstore(0xa0, mload(G1_Y_MPTR))"),
            format!("success := ec_mul_tmp(success, sub(r, mload(R_EVAL_MPTR)))"),
            format!("success := ec_add_acc(success, mload(0x80), mload(0xa0))"),
            format!("mstore(0x80, {})", w.x()),
            format!("mstore(0xa0, {})", w.y()),
            format!("success := ec_mul_tmp(success, sub(r, mload({vanishing_0_mptr})))"),
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
