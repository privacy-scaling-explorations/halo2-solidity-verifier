use crate::{
    codegen::{
        evaluator::Evaluator,
        pcs::{
            bdfg21_computations, queries, rotation_sets,
            BatchOpenScheme::{Bdfg21, Gwc19},
        },
        template::{Halo2Verifier, Halo2VerifyingKey},
        util::{ConstraintSystemMeta, Data, Ptr},
    },
    fe_to_u256, g1_to_u256, g2_to_u256,
};
use halo2_proofs::{
    arithmetic::Field,
    halo2curves::{ff::PrimeField, pairing::MultiMillerLoop, serde::SerdeObject, CurveAffine},
    plonk::VerifyingKey,
    poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG, Rotation},
};
use itertools::{chain, Itertools};
use ruint::aliases::U256;
use std::fmt::{self, Debug};

mod evaluator;
mod pcs;
mod template;
mod util;

pub use pcs::BatchOpenScheme;

#[derive(Debug)]
pub struct SolidityGenerator<'a, C: CurveAffine> {
    vk: &'a VerifyingKey<C>,
    meta: ConstraintSystemMeta,
    num_instances: usize,
    acc_encoding: Option<AccumulatorEncoding>,
    scheme: BatchOpenScheme,
    g1: [U256; 2],
    g2: [U256; 4],
    neg_s_g2: [U256; 4],
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
        scheme: BatchOpenScheme,
    ) -> Self
    where
        C::Base: PrimeField<Repr = [u8; 0x20]>,
        M: Debug,
        M::Scalar: PrimeField,
        M::G1Affine: SerdeObject,
        M::G2Affine: SerdeObject,
    {
        assert_ne!(vk.cs().num_advice_columns(), 0);
        assert_eq!(
            vk.cs().num_instance_columns(),
            1,
            "Multiple instance columns is not yet implemented"
        );
        assert!(
            !vk.cs()
                .instance_queries()
                .iter()
                .any(|(_, rotation)| *rotation != Rotation::cur()),
            "Rotated query to instance column is not yet implemented"
        );
        assert_eq!(
            scheme,
            BatchOpenScheme::Bdfg21,
            "BatchOpenScheme::Gwc19 is not yet implemented"
        );

        let meta = ConstraintSystemMeta::new(vk.cs());

        let g1 = param.get_g()[0];
        let g1 = g1_to_u256(g1);
        let g2 = g2_to_u256(param.g2());
        let neg_s_g2 = g2_to_u256(-param.s_g2());

        Self {
            vk,
            meta,
            num_instances,
            acc_encoding,
            scheme,
            g1,
            g2,
            neg_s_g2,
        }
    }
}

impl<'a, C: CurveAffine> SolidityGenerator<'a, C>
where
    C::Base: PrimeField<Repr = [u8; 0x20]>,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
{
    pub fn render_into(&self, verifier_writer: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        self.generate_verifier(false).render(verifier_writer)
    }

    pub fn render(&self) -> Result<String, fmt::Error> {
        let mut verifier_output = String::new();
        self.render_into(&mut verifier_output)?;
        Ok(verifier_output)
    }

    pub fn render_into_separately(
        &self,
        verifier_writer: &mut impl fmt::Write,
        vk_writer: &mut impl fmt::Write,
    ) -> Result<(), fmt::Error> {
        self.generate_verifier(true).render(verifier_writer)?;
        self.generate_vk().render(vk_writer)?;
        Ok(())
    }

    pub fn render_separately(&self) -> Result<(String, String), fmt::Error> {
        let mut verifier_output = String::new();
        let mut vk_output = String::new();
        self.render_into_separately(&mut verifier_output, &mut vk_output)?;
        Ok((verifier_output, vk_output))
    }

    fn generate_vk(&self) -> Halo2VerifyingKey {
        let constants = {
            let domain = self.vk.get_domain();
            let vk_digest = fe_to_u256(self.vk.transcript_repr());
            let k = U256::from(domain.k());
            let n_inv = fe_to_u256(C::Scalar::from(1 << domain.k()).invert().unwrap());
            let omega = fe_to_u256(domain.get_omega());
            let omega_inv = fe_to_u256(domain.get_omega_inv());
            let omega_inv_to_l = {
                let l = self.meta.rotation_last.unsigned_abs() as u64;
                fe_to_u256(domain.get_omega_inv().pow_vartime([l]))
            };
            let num_instances = U256::from(self.num_instances);
            let has_accumulator = U256::from(self.acc_encoding.is_some());
            let acc_offset = self
                .acc_encoding
                .map(|acc_encoding| U256::from(acc_encoding.offset))
                .unwrap_or_default();
            let num_acc_limbs = self
                .acc_encoding
                .map(|acc_encoding| U256::from(acc_encoding.num_limbs))
                .unwrap_or_default();
            let num_acc_limb_bits = self
                .acc_encoding
                .map(|acc_encoding| U256::from(acc_encoding.num_limb_bits))
                .unwrap_or_default();
            chain![[
                ("vk_digest", vk_digest),
                ("k", k),
                ("n_inv", n_inv),
                ("omega", omega),
                ("omega_inv", omega_inv),
                ("omega_inv_to_l", omega_inv_to_l),
                ("num_instances", num_instances),
                ("has_accumulator", has_accumulator),
                ("acc_offset", acc_offset),
                ("num_acc_limbs", num_acc_limbs),
                ("num_acc_limb_bits", num_acc_limb_bits),
                ("g1_x", self.g1[0]),
                ("g1_y", self.g1[1]),
                ("g2_x_1", self.g2[0]),
                ("g2_x_2", self.g2[1]),
                ("g2_y_1", self.g2[2]),
                ("g2_y_2", self.g2[3]),
                ("neg_s_g2_x_1", self.neg_s_g2[0]),
                ("neg_s_g2_x_2", self.neg_s_g2[1]),
                ("neg_s_g2_y_1", self.neg_s_g2[2]),
                ("neg_s_g2_y_2", self.neg_s_g2[3]),
            ],]
            .collect()
        };
        let fixed_comms = chain![self.vk.fixed_commitments()]
            .flat_map(g1_to_u256::<C>)
            .tuples()
            .collect();
        let permutation_comms = chain![self.vk.permutation().commitments()]
            .flat_map(g1_to_u256::<C>)
            .tuples()
            .collect();
        Halo2VerifyingKey {
            constants,
            fixed_comms,
            permutation_comms,
        }
    }

    fn generate_verifier(&self, separate: bool) -> Halo2Verifier {
        let proof_cptr = Ptr::from(if separate { 0x84 } else { 0x64 });

        let vk = self.generate_vk();
        let vk_len = vk.len();
        let vk_mptr = Ptr::from(self.estimate_working_memory_size(&vk, proof_cptr));
        let data = Data::new(&self.meta, self.scheme, &vk, vk_mptr, proof_cptr);

        let evaluator = Evaluator::new(self.vk.cs(), &self.meta, &data);
        let quotient_eval_numer_computations = chain![
            evaluator.gate_computations(),
            evaluator.permutation_computations(),
            evaluator.lookup_computations()
        ]
        .enumerate()
        .map(|(idx, (mut lines, var))| {
            let line = if idx == 0 {
                format!("quotient_eval_numer := {var}")
            } else {
                format!(
                    "quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), {var}, r)"
                )
            };
            lines.push(line);
            lines
        })
        .collect();

        let pcs_computations = match self.scheme {
            Bdfg21 => bdfg21_computations(&self.meta, &data),
            Gwc19 => unimplemented!(),
        };

        Halo2Verifier {
            scheme: self.scheme,
            vk: (!separate).then_some(vk),
            vk_len,
            vk_mptr,
            num_neg_lagranges: self.meta.rotation_last.unsigned_abs() as usize,
            num_advices: self.meta.num_advices(),
            num_challenges: self.meta.num_challenges(),
            num_evals: self.meta.num_evals,
            num_quotients: self.meta.num_quotients,
            proof_cptr,
            quotient_comm_cptr: data.quotient_comm_cptr,
            proof_len: self.meta.proof_len(self.scheme),
            challenge_mptr: data.challenge_mptr,
            theta_mptr: data.theta_mptr,
            instance_eval_mptr: data.instance_eval_mptr,
            quotient_eval_numer_computations,
            pcs_computations,
        }
    }

    fn estimate_working_memory_size(&self, vk: &Halo2VerifyingKey, proof_cptr: Ptr) -> usize {
        match self.scheme {
            Bdfg21 => {
                let mock_vk_mptr = Ptr::from(0x100000);
                let mock = Data::new(&self.meta, self.scheme, vk, mock_vk_mptr, proof_cptr);
                let (superset, sets) = rotation_sets(&queries(&self.meta, &mock));
                let num_coeffs = sets.iter().map(|set| set.rots().len()).sum::<usize>();
                itertools::max(chain![
                    self.meta
                        .num_advices()
                        .into_iter()
                        .map(|n| (n * 0x40) + 0x20),
                    [
                        (self.meta.num_evals + 1) * 0x20,
                        (2 * (1 + num_coeffs) + 6 + 2 * superset.len() + 2 * sets.len()) * 0x20
                    ],
                ])
                .unwrap()
            }
            Gwc19 => unimplemented!(),
        }
    }
}
