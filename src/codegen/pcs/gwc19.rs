#![allow(clippy::useless_format)]

use crate::codegen::{
    pcs::{queries, Query},
    util::{
        for_loop, group_backward_adjacent_ec_points, group_backward_adjacent_words,
        ConstraintSystemMeta, Data, EcPoint, Location, Ptr, Word,
    },
};
use itertools::{chain, izip, Itertools};
use std::collections::BTreeMap;

pub(super) fn static_working_memory_size(meta: &ConstraintSystemMeta, _: &Data) -> usize {
    0x100 + meta.num_rotations * 0x40
}

pub(super) fn computations(meta: &ConstraintSystemMeta, data: &Data) -> Vec<Vec<String>> {
    let sets = rotation_sets(&queries(meta, data));
    let rots = sets.iter().map(|set| set.rot).collect_vec();
    let (min_rot, max_rot) = rots
        .iter()
        .copied()
        .minmax()
        .into_option()
        .unwrap_or_default();

    let ws = EcPoint::range(data.w_cptr).take(sets.len()).collect_vec();

    let point_w_mptr = Ptr::memory(0x100);
    let point_ws = izip!(rots, EcPoint::range(point_w_mptr)).collect::<BTreeMap<_, _>>();

    let eval_computations = {
        chain![
            [
                "let nu := mload(NU_MPTR)",
                "let mu := mload(MU_MPTR)",
                "let eval_acc",
                "let eval_tmp",
            ]
            .map(str::to_string),
            sets.iter().enumerate().rev().flat_map(|(set_idx, set)| {
                let is_last_set = set_idx == sets.len() - 1;
                let eval_acc = &format!("eval_{}", if is_last_set { "acc" } else { "tmp" });
                let eval_groups = group_backward_adjacent_words(set.evals().iter().rev().skip(1));

                chain![
                    set.evals()
                        .last()
                        .map(|eval| format!("{eval_acc} := {}", eval)),
                    eval_groups.iter().flat_map(|(loc, evals)| {
                        if evals.len() < 3 {
                            evals
                                .iter()
                                .map(|eval| {
                                    format!(
                                        "{eval_acc} := addmod(mulmod({eval_acc}, nu, r), {eval}, r)"
                                    )
                                })
                                .collect_vec()
                        } else {
                            assert_eq!(*loc, Location::Calldata);
                            let eval = "calldataload(cptr)";
                            for_loop(
                                [
                                    format!("let cptr := {}", evals[0].ptr()),
                                    format!("let cptr_end := {}", evals[0].ptr() - evals.len()),
                                ],
                                "lt(cptr_end, cptr)",
                                ["cptr := sub(cptr, 0x20)"],
                                [format!(
                                    "{eval_acc} := addmod(mulmod({eval_acc}, nu, r), {eval}, r)"
                                )],
                            )
                        }
                    }),
                    (!is_last_set)
                        .then_some([
                            "eval_acc := mulmod(eval_acc, mu, r)",
                            "eval_acc := addmod(eval_acc, eval_tmp, r)",
                        ])
                        .into_iter()
                        .flatten()
                        .map(str::to_string),
                ]
                .collect_vec()
            }),
            ["mstore(G1_SCALAR_MPTR, sub(r, eval_acc))".to_string()],
        ]
        .collect_vec()
    };

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
                point_ws
                    .get(&rot)
                    .map(|point| format!("mstore({}, x_pow_of_omega)", point.x().ptr())),
                (rot != max_rot)
                    .then(|| "x_pow_of_omega := mulmod(x_pow_of_omega, omega, r)".to_string())
            ]
        }),
        [
            format!("mstore({}, x)", point_ws[&0].x().ptr()),
            format!("x_pow_of_omega := mulmod(x, omega_inv, r)")
        ],
        (min_rot..0).rev().flat_map(|rot| {
            chain![
                point_ws
                    .get(&rot)
                    .map(|point| format!("mstore({}, x_pow_of_omega)", point.x().ptr())),
                (rot != min_rot).then(|| {
                    "x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)".to_string()
                })
            ]
        })
    ]
    .collect_vec();

    let point_w_computations = for_loop(
        [
            format!("let cptr := {}", data.w_cptr),
            format!("let mptr := {point_w_mptr}"),
            format!("let mptr_end := {}", point_w_mptr + 2 * sets.len()),
        ],
        "lt(mptr, mptr_end)".to_string(),
        ["mptr := add(mptr, 0x40)", "cptr := add(cptr, 0x40)"].map(str::to_string),
        [
            "mstore(0x00, calldataload(cptr))",
            "mstore(0x20, calldataload(add(cptr, 0x20)))",
            "success := ec_mul_acc(success, mload(mptr))",
            "mstore(mptr, mload(0x00))",
            "mstore(add(mptr, 0x20), mload(0x20))",
        ]
        .map(str::to_string),
    );

    let pairing_lhs_computations = chain![
        ["let nu := mload(NU_MPTR)", "let mu := mload(MU_MPTR)"].map(str::to_string),
        sets.iter().enumerate().rev().flat_map(|(set_idx, set)| {
            let is_last_set = set_idx == sets.len() - 1;
            let ec_add = &format!("ec_add_{}", if is_last_set { "acc" } else { "tmp" });
            let ec_mul = &format!("ec_mul_{}", if is_last_set { "acc" } else { "tmp" });
            let acc_x = Ptr::memory(0x00) + if is_last_set { 0 } else { 4 };
            let acc_y = acc_x + 1;
            let point_w = &point_ws[&set.rot];
            let comm_groups = group_backward_adjacent_ec_points(set.comms().iter().rev().skip(1));

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
                comm_groups.into_iter().flat_map(move |(loc, comms)| {
                    if comms.len() < 3 {
                        comms
                            .iter()
                            .flat_map(|comm| {
                                let (x, y) = (comm.x(), comm.y());
                                [
                                    format!("success := {ec_mul}(success, nu)"),
                                    format!("success := {ec_add}(success, {x}, {y})"),
                                ]
                            })
                            .collect_vec()
                    } else {
                        let ptr = comms.first().unwrap().x().ptr();
                        let ptr_end = ptr - 2 * comms.len();
                        let x = Word::from(Ptr::new(loc, "ptr"));
                        let y = Word::from(Ptr::new(loc, "add(ptr, 0x20)"));
                        for_loop(
                            [
                                format!("let ptr := {ptr}"),
                                format!("let ptr_end := {ptr_end}"),
                            ],
                            "lt(ptr_end, ptr)",
                            ["ptr := sub(ptr, 0x40)".to_string()],
                            [
                                format!("success := {ec_mul}(success, nu)"),
                                format!("success := {ec_add}(success, {x}, {y})"),
                            ],
                        )
                    }
                }),
                [format!(
                    "success := {ec_add}(success, {}, {})",
                    point_w.x(),
                    point_w.y()
                )],
                (!is_last_set)
                    .then_some([
                        "success := ec_mul_acc(success, mu)",
                        "success := ec_add_acc(success, mload(0x80), mload(0xa0))",
                    ])
                    .into_iter()
                    .flatten()
                    .map(str::to_string),
            ]
            .collect_vec()
        }),
        [
            "mstore(0x80, mload(G1_X_MPTR))",
            "mstore(0xa0, mload(G1_Y_MPTR))",
            "success := ec_mul_tmp(success, mload(G1_SCALAR_MPTR))",
            "success := ec_add_acc(success, mload(0x80), mload(0xa0))",
            "mstore(PAIRING_LHS_X_MPTR, mload(0x00))",
            "mstore(PAIRING_LHS_Y_MPTR, mload(0x20))",
        ]
        .map(str::to_string),
    ]
    .collect_vec();

    let pairing_rhs_computations = chain![
        [
            format!("let mu := mload(MU_MPTR)"),
            format!("mstore(0x00, {})", ws.last().unwrap().x()),
            format!("mstore(0x20, {})", ws.last().unwrap().y()),
        ],
        ws.iter()
            .nth_back(1)
            .map(|w_second_last| {
                let x = "calldataload(cptr)";
                let y = "calldataload(add(cptr, 0x20))";
                for_loop(
                    [
                        format!("let cptr := {}", w_second_last.x().ptr()),
                        format!("let cptr_end := {}", ws[0].x().ptr() - 1),
                    ],
                    "lt(cptr_end, cptr)",
                    ["cptr := sub(cptr, 0x40)"],
                    [
                        format!("success := ec_mul_acc(success, mu)"),
                        format!("success := ec_add_acc(success, {x}, {y})"),
                    ],
                )
            })
            .into_iter()
            .flatten(),
        [
            format!("mstore(PAIRING_RHS_X_MPTR, mload(0x00))"),
            format!("mstore(PAIRING_RHS_Y_MPTR, mload(0x20))"),
        ],
    ]
    .collect_vec();

    vec![
        eval_computations,
        point_computations,
        point_w_computations,
        pairing_lhs_computations,
        pairing_rhs_computations,
    ]
}

#[derive(Debug)]
struct RotationSet {
    rot: i32,
    comms: Vec<EcPoint>,
    evals: Vec<Word>,
}

impl RotationSet {
    fn comms(&self) -> &[EcPoint] {
        &self.comms
    }

    fn evals(&self) -> &[Word] {
        &self.evals
    }
}

fn rotation_sets(queries: &[Query]) -> Vec<RotationSet> {
    queries.iter().fold(Vec::new(), |mut sets, query| {
        if let Some(pos) = sets.iter().position(|set| set.rot == query.rot) {
            sets[pos].comms.push(query.comm);
            sets[pos].evals.push(query.eval);
        } else {
            sets.push(RotationSet {
                rot: query.rot,
                comms: vec![query.comm],
                evals: vec![query.eval],
            });
        }
        sets
    })
}
