use crate::codegen::{
    evaluator::Evaluator,
    pcs::{
        bdfg21_computations, queries, rotation_sets,
        BatchOpenScheme::{Bdfg21, Gwc19},
    },
    template::{Halo2Verifier, Halo2VerifyingKey},
    util::{fr_to_u256, g1_to_u256s, g2_to_u256s, ConstraintSystemMeta, Data, Ptr},
};
use halo2_proofs::{
    halo2curves::{bn256, ff::Field},
    plonk::VerifyingKey,
    poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG, Rotation},
};
use itertools::{chain, Itertools};
use ruint::aliases::U256;
use std::fmt::{self, Debug};

mod evaluator;
mod pcs;
mod template;
pub(crate) mod util;

pub use pcs::BatchOpenScheme;

/// Solidity verifier generator for [`halo2`] proof with KZG polynomial commitment scheme on BN254.
#[derive(Debug)]
pub struct SolidityGenerator<'a> {
    params: &'a ParamsKZG<bn256::Bn256>,
    vk: &'a VerifyingKey<bn256::G1Affine>,
    scheme: BatchOpenScheme,
    num_instances: usize,
    acc_encoding: Option<AccumulatorEncoding>,
    meta: ConstraintSystemMeta,
}

/// KZG accumulator encoding information.
/// Limbs of each field element are assumed to be least significant limb first.
///
/// Given instances and `AccumulatorEncoding`, the accumulator will be interpreted as below:
/// ```rust
/// use halo2_proofs::halo2curves::{bn256, ff::{Field, PrimeField}, CurveAffine};
///
/// fn accumulator_from_limbs(
///     instances: &[bn256::Fr],
///     offset: usize,
///     num_limbs: usize,
///     num_limb_bits: usize,
/// ) -> (bn256::G1Affine, bn256::G1Affine) {
///     let limbs = |offset| &instances[offset..offset + num_limbs];
///     let acc_lhs_x = fe_from_limbs(limbs(offset), num_limb_bits);
///     let acc_lhs_y = fe_from_limbs(limbs(offset + num_limbs), num_limb_bits);
///     let acc_rhs_x = fe_from_limbs(limbs(offset + 2 * num_limbs), num_limb_bits);
///     let acc_rhs_y = fe_from_limbs(limbs(offset + 3 * num_limbs), num_limb_bits);
///     let acc_lhs = bn256::G1Affine::from_xy(acc_lhs_x, acc_lhs_y).unwrap();
///     let acc_rhs = bn256::G1Affine::from_xy(acc_rhs_x, acc_rhs_y).unwrap();
///     (acc_lhs, acc_rhs)
/// }
///
/// fn fe_from_limbs(limbs: &[bn256::Fr], num_limb_bits: usize) -> bn256::Fq {
///     limbs.iter().rev().fold(bn256::Fq::ZERO, |acc, limb| {
///         acc * bn256::Fq::from(2).pow_vartime([num_limb_bits as u64])
///             + bn256::Fq::from_repr_vartime(limb.to_repr()).unwrap()
///     })
/// }
/// ```
///
/// In the end of `verifyProof`, the accumulator will be used to do batched pairing with the
/// pairing input of incoming proof.
#[derive(Clone, Copy, Debug)]
pub struct AccumulatorEncoding {
    /// Offset of accumulator limbs in instances.
    pub offset: usize,
    /// Number of limbs per base field element.
    pub num_limbs: usize,
    /// Number of bits per limb.
    pub num_limb_bits: usize,
}

impl AccumulatorEncoding {
    /// Return a new `AccumulatorEncoding`.
    pub fn new(offset: usize, num_limbs: usize, num_limb_bits: usize) -> Self {
        Self {
            offset,
            num_limbs,
            num_limb_bits,
        }
    }
}

impl<'a> SolidityGenerator<'a> {
    /// Return a new `SolidityGenerator`.
    pub fn new(
        params: &'a ParamsKZG<bn256::Bn256>,
        vk: &'a VerifyingKey<bn256::G1Affine>,
        scheme: BatchOpenScheme,
        num_instances: usize,
    ) -> Self {
        assert_ne!(vk.cs().num_advice_columns(), 0);
        assert!(
            vk.cs().num_instance_columns() <= 1,
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

        Self {
            params,
            vk,
            scheme,
            num_instances,
            acc_encoding: None,
            meta: ConstraintSystemMeta::new(vk.cs()),
        }
    }

    /// Set `AccumulatorEncoding`.
    pub fn set_acc_encoding(mut self, acc_encoding: Option<AccumulatorEncoding>) -> Self {
        self.acc_encoding = acc_encoding;
        self
    }
}

impl<'a> SolidityGenerator<'a> {
    /// Render `Halo2Verifier.sol` with verifying key embedded into writer.
    pub fn render_into(&self, verifier_writer: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        self.generate_verifier(false).render(verifier_writer)
    }

    /// Render `Halo2Verifier.sol` with verifying key embedded and return it as `String`.
    pub fn render(&self) -> Result<String, fmt::Error> {
        let mut verifier_output = String::new();
        self.render_into(&mut verifier_output)?;
        Ok(verifier_output)
    }

    /// Render `Halo2Verifier.sol` and `Halo2VerifyingKey.sol` into writers.
    pub fn render_separately_into(
        &self,
        verifier_writer: &mut impl fmt::Write,
        vk_writer: &mut impl fmt::Write,
    ) -> Result<(), fmt::Error> {
        self.generate_verifier(true).render(verifier_writer)?;
        self.generate_vk().render(vk_writer)?;
        Ok(())
    }

    /// Render `Halo2Verifier.sol` and `Halo2VerifyingKey.sol` and return them as `String`.
    pub fn render_separately(&self) -> Result<(String, String), fmt::Error> {
        let mut verifier_output = String::new();
        let mut vk_output = String::new();
        self.render_separately_into(&mut verifier_output, &mut vk_output)?;
        Ok((verifier_output, vk_output))
    }

    fn generate_vk(&self) -> Halo2VerifyingKey {
        let constants = {
            let domain = self.vk.get_domain();
            let vk_digest = fr_to_u256(vk_transcript_repr(self.vk));
            let k = U256::from(domain.k());
            let n_inv = fr_to_u256(bn256::Fr::from(1 << domain.k()).invert().unwrap());
            let omega = fr_to_u256(domain.get_omega());
            let omega_inv = fr_to_u256(domain.get_omega_inv());
            let omega_inv_to_l = {
                let l = self.meta.rotation_last.unsigned_abs() as u64;
                fr_to_u256(domain.get_omega_inv().pow_vartime([l]))
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
            let g1 = self.params.get_g()[0];
            let g1 = g1_to_u256s(g1);
            let g2 = g2_to_u256s(self.params.g2());
            let neg_s_g2 = g2_to_u256s(-self.params.s_g2());
            vec![
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
                ("g1_x", g1[0]),
                ("g1_y", g1[1]),
                ("g2_x_1", g2[0]),
                ("g2_x_2", g2[1]),
                ("g2_y_1", g2[2]),
                ("g2_y_2", g2[3]),
                ("neg_s_g2_x_1", neg_s_g2[0]),
                ("neg_s_g2_x_2", neg_s_g2[1]),
                ("neg_s_g2_y_1", neg_s_g2[2]),
                ("neg_s_g2_y_2", neg_s_g2[3]),
            ]
        };
        let fixed_comms = chain![self.vk.fixed_commitments()]
            .flat_map(g1_to_u256s)
            .tuples()
            .collect();
        let permutation_comms = chain![self.vk.permutation().commitments()]
            .flat_map(g1_to_u256s)
            .tuples()
            .collect();
        Halo2VerifyingKey {
            constants,
            fixed_comms,
            permutation_comms,
        }
    }

    fn generate_verifier(&self, separate: bool) -> Halo2Verifier {
        let proof_cptr = Ptr::calldata(if separate { 0x84 } else { 0x64 });

        let vk = self.generate_vk();
        let vk_len = vk.len();
        let vk_mptr = Ptr::memory(self.estimate_static_working_memory_size(&vk, proof_cptr));
        let data = Data::new(&self.meta, &vk, vk_mptr, proof_cptr);

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
            quotient_eval_numer_computations,
            pcs_computations,
        }
    }

    fn estimate_static_working_memory_size(
        &self,
        vk: &Halo2VerifyingKey,
        proof_cptr: Ptr,
    ) -> usize {
        let pcs_computation = match self.scheme {
            Bdfg21 => {
                let mock_vk_mptr = Ptr::memory(0x100000);
                let mock = Data::new(&self.meta, vk, mock_vk_mptr, proof_cptr);
                let (superset, sets) = rotation_sets(&queries(&self.meta, &mock));
                let num_coeffs = sets.iter().map(|set| set.rots().len()).sum::<usize>();
                2 * (1 + num_coeffs) + 6 + 2 * superset.len() + 1 + 3 * sets.len()
            }
            Gwc19 => unimplemented!(),
        };

        itertools::max(chain![
            // Hashing advice commitments
            chain![self.meta.num_advices().into_iter()].map(|n| n * 2 + 1),
            // Hashing evaluations
            [self.meta.num_evals + 1],
            // PCS computation
            [pcs_computation],
            // Pairing
            [12],
        ])
        .unwrap()
            * 0x20
    }
}

// Remove when `vk.transcript_repr()` is ready for usage.
fn vk_transcript_repr(vk: &VerifyingKey<bn256::G1Affine>) -> bn256::Fr {
    use blake2b_simd::Params;
    use halo2_proofs::halo2curves::ff::FromUniformBytes;

    let fmtted_pinned_vk = format!("{:?}", vk.pinned());
    let mut hasher = Params::new()
        .hash_length(64)
        .personal(b"Halo2-Verify-Key")
        .to_state();
    hasher
        .update(&(fmtted_pinned_vk.len() as u64).to_le_bytes())
        .update(fmtted_pinned_vk.as_bytes());
    FromUniformBytes::from_uniform_bytes(hasher.finalize().as_array())
}
