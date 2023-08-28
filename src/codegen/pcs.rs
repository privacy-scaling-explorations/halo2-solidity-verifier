use crate::codegen::{calldataload_asm, mload_asm};
use halo2_proofs::{halo2curves::CurveAffine, plonk::VerifyingKey};
use itertools::{chain, Itertools};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Comm {
    Memory(usize),
    Calldata(usize),
    Asm(String, String),
}

impl Comm {
    pub fn x_asm(&self) -> String {
        match self {
            Comm::Memory(mptr) => mload_asm(*mptr),
            Comm::Calldata(cptr) => calldataload_asm(*cptr),
            Comm::Asm(x, _) => x.clone(),
        }
    }

    pub fn y_asm(&self) -> String {
        match self {
            Comm::Memory(mptr) => mload_asm(mptr + 0x20),
            Comm::Calldata(cptr) => calldataload_asm(cptr + 0x20),
            Comm::Asm(_, y) => y.clone(),
        }
    }
}

#[derive(Debug)]
pub struct Query {
    comm: Comm,
    rotation: i32,
    eval_asm: String,
}

pub fn queries<C: CurveAffine>(
    vk: &VerifyingKey<C>,
    proof_cptr: usize,
    fixed_comm_mptr: usize,
) -> Vec<Query> {
    let rotation_last = -(vk.cs().blinding_factors() as i32 + 1);

    let num_fixeds = vk.cs().num_fixed_columns();
    let num_permutations = vk.cs().permutation().get_columns().len();
    let num_advices = vk.cs().num_advice_columns();
    let num_lookup_permuteds = 2 * vk.cs().lookups().len();
    let num_permutation_zs = vk
        .cs()
        .permutation()
        .get_columns()
        .chunks(vk.cs().degree() - 2)
        .count();
    let num_lookup_zs = vk.cs().lookups().len();
    let num_quotients = vk.get_domain().get_quotient_poly_degree();

    let permutation_comm_mptr = fixed_comm_mptr + num_fixeds * 0x40;
    let advice_comm_cptr = proof_cptr;
    let lookup_permuted_comm_cptr = advice_comm_cptr + num_advices * 0x40;
    let permutation_z_comm_cptr = lookup_permuted_comm_cptr + num_lookup_permuteds * 0x40;
    let lookup_z_comm_cptr = permutation_z_comm_cptr + num_permutation_zs * 0x40;
    let random_comm_cptr = lookup_z_comm_cptr + num_lookup_zs * 0x40;
    let quotient_comm_cptr = random_comm_cptr + 0x40;

    let advice_eval_cptr = quotient_comm_cptr + num_quotients * 0x40;
    let fixed_eval_cptr = advice_eval_cptr + vk.cs().advice_queries().len() * 0x20;
    let random_eval_cptr = fixed_eval_cptr + vk.cs().fixed_queries().len() * 0x20;
    let permutation_eval_cptr = random_eval_cptr + 0x20;
    let permutation_z_eval_cptr = permutation_eval_cptr + num_permutations * 0x20;
    let lookup_eval_cptr = permutation_z_eval_cptr + (3 * num_permutation_zs - 1) * 0x20;

    chain![
        vk.cs()
            .advice_queries()
            .iter()
            .enumerate()
            .map(|(idx, (column, rotation))| {
                Query {
                    comm: Comm::Calldata(advice_comm_cptr + column.index() * 0x40),
                    rotation: rotation.0,
                    eval_asm: calldataload_asm(advice_eval_cptr + idx * 0x20),
                }
            }),
        (0..num_permutation_zs).flat_map(|idx| {
            let comm = Comm::Calldata(permutation_z_comm_cptr + idx * 0x40);
            let eval_cptr = permutation_z_eval_cptr + idx * 3 * 0x20;
            [
                Query {
                    comm: comm.clone(),
                    rotation: 0,
                    eval_asm: calldataload_asm(eval_cptr),
                },
                Query {
                    comm,
                    rotation: 1,
                    eval_asm: calldataload_asm(eval_cptr + 0x20),
                },
            ]
        }),
        (0..num_permutation_zs).rev().skip(1).map(|idx| {
            let comm = Comm::Calldata(permutation_z_comm_cptr + idx * 0x40);
            let eval_cptr = permutation_z_eval_cptr + idx * 3 * 0x20;
            Query {
                comm,
                rotation: rotation_last,
                eval_asm: calldataload_asm(eval_cptr + 0x40),
            }
        }),
        (0..num_lookup_zs).flat_map(|idx| {
            let lookup_z_comm_cptr = lookup_z_comm_cptr + idx * 0x40;
            let lookup_permuted_comm_cptr = lookup_permuted_comm_cptr + idx * 2 * 0x40;
            let lookup_eval_cptr = lookup_eval_cptr + idx * 5 * 0x20;
            [
                Query {
                    comm: Comm::Calldata(lookup_z_comm_cptr),
                    rotation: 0,
                    eval_asm: calldataload_asm(lookup_eval_cptr),
                },
                Query {
                    comm: Comm::Calldata(lookup_permuted_comm_cptr),
                    rotation: 0,
                    eval_asm: calldataload_asm(lookup_eval_cptr + 2 * 0x20),
                },
                Query {
                    comm: Comm::Calldata(lookup_permuted_comm_cptr + 0x40),
                    rotation: 0,
                    eval_asm: calldataload_asm(lookup_eval_cptr + 4 * 0x20),
                },
                Query {
                    comm: Comm::Calldata(lookup_permuted_comm_cptr),
                    rotation: -1,
                    eval_asm: calldataload_asm(lookup_eval_cptr + 3 * 0x20),
                },
                Query {
                    comm: Comm::Calldata(lookup_z_comm_cptr),
                    rotation: 1,
                    eval_asm: calldataload_asm(lookup_eval_cptr + 0x20),
                },
            ]
        }),
        vk.cs()
            .fixed_queries()
            .iter()
            .enumerate()
            .map(|(idx, (column, rotation))| {
                Query {
                    comm: Comm::Memory(fixed_comm_mptr + column.index() * 0x40),
                    rotation: rotation.0,
                    eval_asm: calldataload_asm(fixed_eval_cptr + idx * 0x20),
                }
            }),
        (0..num_permutations).map(|idx| {
            Query {
                comm: Comm::Memory(permutation_comm_mptr + idx * 0x40),
                rotation: 0,
                eval_asm: calldataload_asm(permutation_eval_cptr + idx * 0x20),
            }
        }),
        [
            Query {
                comm: Comm::Asm("mload(H_X_MPTR)".to_string(), "mload(H_Y_MPTR)".to_string()),
                rotation: 0,
                eval_asm: "mload(H_EVAL_MPTR)".to_string(),
            },
            Query {
                comm: Comm::Calldata(random_comm_cptr),
                rotation: 0,
                eval_asm: calldataload_asm(random_eval_cptr),
            },
        ]
    ]
    .collect()
}

#[derive(Debug)]
pub struct RotationSet {
    rotations: BTreeSet<i32>,
    diffs: BTreeSet<i32>,
    comms: Vec<Comm>,
    evals: Vec<Vec<String>>,
}

impl RotationSet {
    pub fn rotations(&self) -> &BTreeSet<i32> {
        &self.rotations
    }

    pub fn diffs(&self) -> &BTreeSet<i32> {
        &self.diffs
    }

    pub fn comms(&self) -> &[Comm] {
        &self.comms
    }

    pub fn evals(&self) -> &[Vec<String>] {
        &self.evals
    }
}

pub fn rotation_sets(queries: &[Query]) -> (BTreeSet<i32>, Vec<RotationSet>) {
    let mut superset = BTreeSet::new();
    let comm_queries = queries.iter().fold(
        Vec::<(Comm, BTreeMap<i32, &str>)>::new(),
        |mut comm_queries, query| {
            superset.insert(query.rotation);
            if let Some(pos) = comm_queries
                .iter()
                .position(|(comm, _)| comm == &query.comm)
            {
                let (_, queries) = &mut comm_queries[pos];
                assert!(!queries.contains_key(&query.rotation));
                queries.insert(query.rotation, &query.eval_asm);
            } else {
                comm_queries.push((
                    query.comm.clone(),
                    BTreeMap::from_iter([(query.rotation, query.eval_asm.as_str())]),
                ));
            }
            comm_queries
        },
    );
    let superset = superset;
    let rotation_sets =
        comm_queries
            .into_iter()
            .fold(Vec::<RotationSet>::new(), |mut sets, (comm, queries)| {
                if let Some(pos) = sets
                    .iter()
                    .position(|set| itertools::equal(&set.rotations, queries.keys()))
                {
                    let set = &mut sets[pos];
                    if !set.comms.contains(&comm) {
                        set.comms.push(comm);
                        set.evals
                            .push(queries.into_values().map(ToOwned::to_owned).collect_vec());
                    }
                } else {
                    let diffs = BTreeSet::from_iter(
                        superset
                            .iter()
                            .filter(|rotation| !queries.contains_key(rotation))
                            .copied(),
                    );
                    let set = RotationSet {
                        rotations: BTreeSet::from_iter(queries.keys().copied()),
                        diffs,
                        comms: vec![comm],
                        evals: vec![queries.into_values().map(ToOwned::to_owned).collect()],
                    };
                    sets.push(set);
                }
                sets
            });
    (superset, rotation_sets)
}
