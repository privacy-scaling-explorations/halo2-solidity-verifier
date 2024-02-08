use crate::codegen::util::{ConstraintSystemMeta, Data, EcPoint, Word};
use itertools::{chain, izip};

mod bdfg21;
mod gwc19;

/// KZG batch open schemes in `halo2`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BatchOpenScheme {
    /// Batch open scheme in [Plonk] paper.
    /// Corresponding to `halo2_proofs::poly::kzg::multiopen::ProverGWC`
    ///
    /// [Plonk]: https://eprint.iacr.org/2019/953.pdf
    Gwc19,
    /// Batch open scheme in [BDFG21] paper.
    /// Corresponding to `halo2_proofs::poly::kzg::multiopen::ProverSHPLONK`
    ///
    /// [BDFG21]: https://eprint.iacr.org/2020/081.pdf
    Bdfg21,
}

impl BatchOpenScheme {
    pub(crate) fn static_working_memory_size(
        &self,
        meta: &ConstraintSystemMeta,
        data: &Data,
    ) -> usize {
        match self {
            Self::Bdfg21 => bdfg21::static_working_memory_size(meta, data),
            Self::Gwc19 => gwc19::static_working_memory_size(meta, data),
        }
    }

    pub(crate) fn computations(
        &self,
        meta: &ConstraintSystemMeta,
        data: &Data,
    ) -> Vec<Vec<String>> {
        match self {
            Self::Bdfg21 => bdfg21::computations(meta, data),
            Self::Gwc19 => gwc19::computations(meta, data),
        }
    }
}

#[derive(Debug)]
pub(crate) struct Query {
    comm: EcPoint,
    rot: i32,
    eval: Word,
}

impl Query {
    fn new(comm: EcPoint, rot: i32, eval: Word) -> Self {
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
