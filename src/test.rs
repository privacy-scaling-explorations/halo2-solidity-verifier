use crate::{
    codegen::{AccumulatorEncoding, BatchOpenScheme::Bdfg21, SolidityGenerator},
    encode_calldata,
    evm::test::{compile_solidity, Evm},
    FN_SIG_VERIFY_PROOF, FN_SIG_VERIFY_PROOF_WITH_VK_ADDRESS,
};
use halo2_proofs::halo2curves::bn256::{Bn256, Fr};
use rand::{rngs::StdRng, RngCore, SeedableRng};
use sha3::Digest;
use std::{fs::File, io::Write};

#[test]
fn function_signature() {
    for (fn_name, fn_sig) in [
        ("verifyProof(bytes,uint256[])", FN_SIG_VERIFY_PROOF),
        (
            "verifyProof(address,bytes,uint256[])",
            FN_SIG_VERIFY_PROOF_WITH_VK_ADDRESS,
        ),
    ] {
        assert_eq!(
            <[u8; 32]>::from(sha3::Keccak256::digest(fn_name))[..4],
            fn_sig,
        );
    }
}

#[test]
fn render_huge() {
    run_render::<halo2::huge::HugeCircuit<Bn256>>()
}

#[test]
fn render_maingate() {
    run_render::<halo2::maingate::MainGateWithRange<Bn256>>()
}

#[test]
fn render_separately_huge() {
    run_render_separately::<halo2::huge::HugeCircuit<Bn256>>()
}

#[test]
fn render_separately_maingate() {
    run_render_separately::<halo2::maingate::MainGateWithRange<Bn256>>()
}

fn run_render<C: halo2::TestCircuit<Fr>>() {
    let acc_encoding = AccumulatorEncoding::new(0, 4, 68).into();
    let (params, vk, instances, proof) =
        halo2::create_testdata_bdfg21::<C>(C::min_k(), acc_encoding, std_rng());

    let generator = SolidityGenerator::new(&params, &vk, Bdfg21, instances.len())
        .set_acc_encoding(acc_encoding);
    let verifier_solidity = generator.render().unwrap();
    let verifier_creation_code = compile_solidity(verifier_solidity);
    let verifier_creation_code_size = verifier_creation_code.len();

    let mut evm = Evm::default();
    let verifier_address = evm.create(verifier_creation_code);
    let verifier_runtime_code_size = evm.code_size(verifier_address);

    println!("Verifier creation code size: {verifier_creation_code_size}");
    println!("Verifier runtime code size: {verifier_runtime_code_size}");

    let (gas_cost, output) = evm.call(verifier_address, encode_calldata(None, &proof, &instances));
    assert_eq!(output, [vec![0; 31], vec![1]].concat());
    println!("Gas cost: {gas_cost}");
}

fn run_render_separately<C: halo2::TestCircuit<Fr>>() {
    let acc_encoding = AccumulatorEncoding::new(0, 4, 68).into();
    let (params, vk, instances, _) =
        halo2::create_testdata_bdfg21::<C>(C::min_k(), acc_encoding, std_rng());

    let generator = SolidityGenerator::new(&params, &vk, Bdfg21, instances.len())
        .set_acc_encoding(acc_encoding);
    let (verifier_solidity, _vk_solidity) = generator.render_separately().unwrap();
    let verifier_creation_code = compile_solidity(&verifier_solidity);
    let verifier_creation_code_size = verifier_creation_code.len();

    let mut evm = Evm::default();
    let verifier_address = evm.create(verifier_creation_code);
    let verifier_runtime_code_size = evm.code_size(verifier_address);

    println!("Verifier creation code size: {verifier_creation_code_size}");
    println!("Verifier runtime code size: {verifier_runtime_code_size}");

    let deployed_verifier_solidity = verifier_solidity;

    for k in C::min_k()..C::min_k() + 4 {
        let (params, vk, instances, proof) =
            halo2::create_testdata_bdfg21::<C>(k, acc_encoding, std_rng());
        let generator = SolidityGenerator::new(&params, &vk, Bdfg21, instances.len())
            .set_acc_encoding(acc_encoding);

        let (verifier_solidity, vk_solidity) = generator.render_separately().unwrap();
        assert_eq!(deployed_verifier_solidity, verifier_solidity);

        let vk_creation_code = compile_solidity(&vk_solidity);
        let vk_address = evm.create(vk_creation_code);

        let (gas_cost, output) = evm.call(
            verifier_address,
            encode_calldata(Some(vk_address.into()), &proof, &instances),
        );
        assert_eq!(output, [vec![0; 31], vec![1]].concat());
        println!("Gas cost: {gas_cost}");
    }
}

fn std_rng() -> impl RngCore + Clone {
    StdRng::seed_from_u64(0)
}

#[allow(dead_code)]
fn save_generated(verifier: &str, vk: Option<&str>) {
    const DIR_GENERATED: &str = "./target/generated";

    std::fs::create_dir_all(DIR_GENERATED).unwrap();
    File::create(format!("{DIR_GENERATED}/Halo2Verifier.sol"))
        .unwrap()
        .write_all(verifier.as_bytes())
        .unwrap();
    if let Some(vk) = vk {
        File::create(format!("{DIR_GENERATED}/Halo2VerifyingKey.sol"))
            .unwrap()
            .write_all(vk.as_bytes())
            .unwrap();
    }
}

mod halo2 {
    use crate::{codegen::AccumulatorEncoding, transcript::Keccak256Transcript};
    use halo2_proofs::{
        arithmetic::CurveAffine,
        halo2curves::{
            bn256,
            ff::{Field, PrimeField},
            group::{prime::PrimeCurveAffine, Curve, Group},
            pairing::{MillerLoopResult, MultiMillerLoop},
        },
        plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, VerifyingKey},
        poly::kzg::{
            commitment::ParamsKZG,
            multiopen::{ProverSHPLONK, VerifierSHPLONK},
            strategy::SingleStrategy,
        },
        transcript::TranscriptWriterBuffer,
    };
    use itertools::Itertools;
    use rand::RngCore;
    use ruint::aliases::U256;
    use std::borrow::Borrow;

    pub trait TestCircuit<F: Field>: Circuit<F> {
        fn min_k() -> u32;

        fn new(acc_encoding: Option<AccumulatorEncoding>, rng: impl RngCore) -> Self;

        fn instances(&self) -> Vec<F>;
    }

    #[allow(clippy::type_complexity)]
    pub fn create_testdata_bdfg21<C: TestCircuit<bn256::Fr>>(
        k: u32,
        acc_encoding: Option<AccumulatorEncoding>,
        mut rng: impl RngCore + Clone,
    ) -> (
        ParamsKZG<bn256::Bn256>,
        VerifyingKey<bn256::G1Affine>,
        Vec<bn256::Fr>,
        Vec<u8>,
    ) {
        let circuit = C::new(acc_encoding, rng.clone());
        let instances = circuit.instances();

        let params = ParamsKZG::<bn256::Bn256>::setup(k, &mut rng);
        let vk = keygen_vk(&params, &circuit).unwrap();
        let pk = keygen_pk(&params, vk.clone(), &circuit).unwrap();

        let proof = {
            let mut transcript = Keccak256Transcript::new(Vec::new());
            create_proof::<_, ProverSHPLONK<_>, _, _, _, _>(
                &params,
                &pk,
                &[circuit],
                &[&[&instances]],
                &mut rng,
                &mut transcript,
            )
            .unwrap();
            transcript.finalize()
        };

        let result = {
            let mut transcript = Keccak256Transcript::new(proof.as_slice());
            verify_proof::<_, VerifierSHPLONK<_>, _, _, SingleStrategy<_>>(
                &params,
                pk.get_vk(),
                SingleStrategy::new(&params),
                &[&[&instances]],
                &mut transcript,
            )
        };
        assert!(result.is_ok());

        (params, vk, instances, proof)
    }

    fn random_accumulator_limbs<M>(
        acc_encoding: AccumulatorEncoding,
        mut rng: impl RngCore,
    ) -> Vec<M::Scalar>
    where
        M: MultiMillerLoop,
        <M::G1Affine as CurveAffine>::Base: PrimeField<Repr = [u8; 0x20]>,
        M::Scalar: PrimeField<Repr = [u8; 0x20]>,
    {
        let s = M::Scalar::random(&mut rng);
        let g1 = M::G1Affine::generator();
        let g2 = M::G2Affine::generator();
        let neg_s_g2 = (g2 * -s).to_affine();
        let lhs_scalar = M::Scalar::random(&mut rng);
        let rhs_scalar = lhs_scalar * s.invert().unwrap();
        let [lhs, rhs] = [lhs_scalar, rhs_scalar].map(|scalar| (g1 * scalar).to_affine());

        assert!(bool::from(
            M::multi_miller_loop(&[(&lhs, &g2.into()), (&rhs, &neg_s_g2.into())])
                .final_exponentiation()
                .is_identity()
        ));

        [lhs, rhs]
            .into_iter()
            .flat_map(|ec_point| ec_point_to_limbs(ec_point, acc_encoding.num_limb_bits))
            .collect()
    }

    fn ec_point_to_limbs<C>(ec_point: impl Borrow<C>, num_limb_bits: usize) -> Vec<C::Scalar>
    where
        C: CurveAffine,
        C::Base: PrimeField<Repr = [u8; 0x20]>,
        C::Scalar: PrimeField<Repr = [u8; 0x20]>,
    {
        let coords = ec_point.borrow().coordinates().unwrap();
        [*coords.x(), *coords.y()]
            .into_iter()
            .flat_map(|coord| fe_to_limbs(coord, num_limb_bits))
            .collect()
    }

    fn fe_to_limbs<F1, F2>(fe: impl Borrow<F1>, num_limb_bits: usize) -> Vec<F2>
    where
        F1: PrimeField<Repr = [u8; 0x20]>,
        F2: PrimeField<Repr = [u8; 0x20]>,
    {
        let big = U256::from_le_bytes(fe.borrow().to_repr());
        let mask = &((U256::from(1) << num_limb_bits) - U256::from(1));
        (0usize..)
            .step_by(num_limb_bits)
            .map(|shift| fe_from_u256((big >> shift) & mask))
            .take((F1::NUM_BITS as usize + num_limb_bits - 1) / num_limb_bits)
            .collect_vec()
    }

    fn fe_from_u256<F>(u256: impl Borrow<U256>) -> F
    where
        F: PrimeField<Repr = [u8; 0x20]>,
    {
        let bytes = u256.borrow().to_le_bytes::<32>();
        F::from_repr_vartime(bytes).unwrap()
    }

    pub mod huge {
        use crate::{
            codegen::AccumulatorEncoding,
            test::halo2::{random_accumulator_limbs, TestCircuit},
        };
        use halo2_proofs::{
            arithmetic::CurveAffine,
            circuit::{Layouter, SimpleFloorPlanner, Value},
            halo2curves::{
                ff::{Field, PrimeField},
                pairing::MultiMillerLoop,
            },
            plonk::{
                self, Advice, Circuit, Column, ConstraintSystem, Expression, FirstPhase, Fixed,
                Instance, SecondPhase, Selector, ThirdPhase,
            },
            poly::Rotation,
        };
        use itertools::{izip, Itertools};
        use rand::RngCore;
        use std::{array, fmt::Debug, iter, mem};

        #[derive(Clone, Debug, Default)]
        pub struct HugeCircuit<M: MultiMillerLoop>(Vec<M::Scalar>);

        impl<M: MultiMillerLoop> TestCircuit<M::Scalar> for HugeCircuit<M>
        where
            M: MultiMillerLoop,
            <M::G1Affine as CurveAffine>::Base: PrimeField<Repr = [u8; 0x20]>,
            M::Scalar: PrimeField<Repr = [u8; 0x20]>,
        {
            fn min_k() -> u32 {
                6
            }

            fn new(acc_encoding: Option<AccumulatorEncoding>, mut rng: impl RngCore) -> Self {
                let instances = if let Some(acc_encoding) = acc_encoding {
                    random_accumulator_limbs::<M>(acc_encoding, rng)
                } else {
                    iter::repeat_with(|| M::Scalar::random(&mut rng))
                        .take(10)
                        .collect()
                };
                Self(instances)
            }

            fn instances(&self) -> Vec<M::Scalar> {
                self.0.clone()
            }
        }

        impl<M: MultiMillerLoop> Circuit<M::Scalar> for HugeCircuit<M>
        where
            M::Scalar: PrimeField,
        {
            type Config = (
                [Selector; 10],
                [Selector; 10],
                [Column<Fixed>; 10],
                [Column<Advice>; 10],
                Column<Instance>,
            );
            type FloorPlanner = SimpleFloorPlanner;
            #[cfg(feature = "halo2_circuit_params")]
            type Params = ();

            fn without_witnesses(&self) -> Self {
                unimplemented!()
            }

            fn configure(meta: &mut ConstraintSystem<M::Scalar>) -> Self::Config {
                let selectors = [(); 10].map(|_| meta.selector());
                let complex_selectors = [(); 10].map(|_| meta.complex_selector());
                let fixeds = [(); 10].map(|_| meta.fixed_column());
                let (advices, challenges) = (0..10)
                    .map(|idx| match idx % 3 {
                        0 => (
                            meta.advice_column_in(FirstPhase),
                            meta.challenge_usable_after(FirstPhase),
                        ),
                        1 => (
                            meta.advice_column_in(SecondPhase),
                            meta.challenge_usable_after(SecondPhase),
                        ),
                        2 => (
                            meta.advice_column_in(ThirdPhase),
                            meta.challenge_usable_after(ThirdPhase),
                        ),
                        _ => unreachable!(),
                    })
                    .unzip::<_, _, Vec<_>, Vec<_>>();
                let advices: [_; 10] = advices.try_into().unwrap();
                let challenges: [_; 10] = challenges.try_into().unwrap();
                let instance = meta.instance_column();

                meta.create_gate("", |meta| {
                    let selectors = selectors.map(|selector| meta.query_selector(selector));
                    let advices: [Expression<M::Scalar>; 10] = array::from_fn(|idx| {
                        let rotation = Rotation((idx as i32 - advices.len() as i32) / 2);
                        meta.query_advice(advices[idx], rotation)
                    });
                    let challenges = challenges.map(|challenge| meta.query_challenge(challenge));

                    izip!(
                        selectors,
                        advices.iter().cloned(),
                        advices[1..].iter().cloned(),
                        advices[2..].iter().cloned(),
                        challenges.iter().cloned(),
                        challenges[1..].iter().cloned(),
                        challenges[2..].iter().cloned(),
                    )
                    .map(|(q, a1, a2, a3, c1, c2, c3)| q * a1 * a2 * a3 * c1 * c2 * c3)
                    .collect_vec()
                });

                for ((q1, q2, q3), (f1, f2, f3), (a1, a2, a3)) in izip!(
                    complex_selectors.iter().tuple_windows(),
                    fixeds.iter().tuple_windows(),
                    advices.iter().tuple_windows()
                ) {
                    meta.lookup_any("", |meta| {
                        izip!([q1, q2, q3], [f1, f2, f3], [a1, a2, a3])
                            .map(|(q, f, a)| {
                                let q = meta.query_selector(*q);
                                let f = meta.query_fixed(*f, Rotation::cur());
                                let a = meta.query_advice(*a, Rotation::cur());
                                (q * a, f)
                            })
                            .collect_vec()
                    });
                }

                fixeds.map(|column| meta.enable_equality(column));
                advices.map(|column| meta.enable_equality(column));
                meta.enable_equality(instance);

                (selectors, complex_selectors, fixeds, advices, instance)
            }

            fn synthesize(
                &self,
                (selectors, complex_selectors, fixeds, advices, instance): Self::Config,
                mut layouter: impl Layouter<M::Scalar>,
            ) -> Result<(), plonk::Error> {
                let assigneds = layouter.assign_region(
                    || "",
                    |mut region| {
                        let offset = &mut 10;
                        let mut next_offset = || mem::replace(offset, *offset + 1);

                        for q in selectors {
                            q.enable(&mut region, next_offset())?;
                        }
                        for q in complex_selectors {
                            q.enable(&mut region, next_offset())?;
                        }
                        for (idx, column) in izip!(1.., fixeds) {
                            let value = Value::known(M::Scalar::from(idx));
                            region.assign_fixed(|| "", column, next_offset(), || value)?;
                        }
                        izip!(advices, &self.0)
                            .map(|(column, value)| {
                                let value = Value::known(*value);
                                region.assign_advice(|| "", column, next_offset(), || value)
                            })
                            .try_collect::<_, Vec<_>, _>()
                    },
                )?;
                for (idx, assigned) in izip!(0.., assigneds) {
                    layouter.constrain_instance(assigned.cell(), instance, idx)?;
                }
                Ok(())
            }
        }
    }

    pub mod maingate {
        use crate::{
            codegen::AccumulatorEncoding,
            test::halo2::{random_accumulator_limbs, TestCircuit},
        };
        use halo2_maingate::{
            MainGate, MainGateConfig, MainGateInstructions, RangeChip, RangeConfig,
            RangeInstructions, RegionCtx,
        };
        use halo2_proofs::{
            arithmetic::CurveAffine,
            circuit::{Layouter, SimpleFloorPlanner, Value},
            halo2curves::{
                ff::{Field, PrimeField},
                pairing::MultiMillerLoop,
            },
            plonk::{Circuit, ConstraintSystem, Error},
        };
        use itertools::Itertools;
        use rand::RngCore;
        use std::iter;

        #[derive(Clone)]
        pub struct MainGateWithRangeConfig {
            main_gate_config: MainGateConfig,
            range_config: RangeConfig,
        }

        impl MainGateWithRangeConfig {
            fn configure<F: PrimeField>(
                meta: &mut ConstraintSystem<F>,
                composition_bits: Vec<usize>,
                overflow_bits: Vec<usize>,
            ) -> Self {
                let main_gate_config = MainGate::<F>::configure(meta);
                let range_config = RangeChip::<F>::configure(
                    meta,
                    &main_gate_config,
                    composition_bits,
                    overflow_bits,
                );
                MainGateWithRangeConfig {
                    main_gate_config,
                    range_config,
                }
            }

            fn main_gate<F: PrimeField>(&self) -> MainGate<F> {
                MainGate::new(self.main_gate_config.clone())
            }

            fn range_chip<F: PrimeField>(&self) -> RangeChip<F> {
                RangeChip::new(self.range_config.clone())
            }
        }

        #[derive(Clone, Default)]
        pub struct MainGateWithRange<M: MultiMillerLoop> {
            instances: Vec<M::Scalar>,
        }

        impl<M> TestCircuit<M::Scalar> for MainGateWithRange<M>
        where
            M: MultiMillerLoop,
            <M::G1Affine as CurveAffine>::Base: PrimeField<Repr = [u8; 0x20]>,
            M::Scalar: PrimeField<Repr = [u8; 0x20]>,
        {
            fn min_k() -> u32 {
                9
            }

            fn new(acc_encoding: Option<AccumulatorEncoding>, mut rng: impl RngCore) -> Self {
                let instances = if let Some(acc_encoding) = acc_encoding {
                    random_accumulator_limbs::<M>(acc_encoding, rng)
                } else {
                    iter::repeat_with(|| M::Scalar::random(&mut rng))
                        .take(10)
                        .collect()
                };
                Self { instances }
            }

            fn instances(&self) -> Vec<M::Scalar> {
                self.instances.clone()
            }
        }

        impl<M: MultiMillerLoop> Circuit<M::Scalar> for MainGateWithRange<M>
        where
            M::Scalar: PrimeField,
        {
            type Config = MainGateWithRangeConfig;
            type FloorPlanner = SimpleFloorPlanner;
            #[cfg(feature = "halo2_circuit_params")]
            type Params = ();

            fn without_witnesses(&self) -> Self {
                unimplemented!()
            }

            fn configure(meta: &mut ConstraintSystem<M::Scalar>) -> Self::Config {
                MainGateWithRangeConfig::configure(meta, vec![8], vec![4, 7])
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<M::Scalar>,
            ) -> Result<(), Error> {
                let main_gate = config.main_gate();
                let range_chip = config.range_chip();
                range_chip.load_table(&mut layouter)?;

                let advices = layouter.assign_region(
                    || "",
                    |region| {
                        let mut ctx = RegionCtx::new(region, 0);

                        let advices = self
                            .instances
                            .iter()
                            .map(|value| main_gate.assign_value(&mut ctx, Value::known(*value)))
                            .try_collect::<_, Vec<_>, _>()?;

                        // Dummy gates to make all fixed column with values
                        range_chip.decompose(
                            &mut ctx,
                            Value::known(M::Scalar::from(u64::MAX)),
                            8,
                            64,
                        )?;
                        range_chip.decompose(
                            &mut ctx,
                            Value::known(M::Scalar::from(u32::MAX as u64)),
                            8,
                            39,
                        )?;
                        let a = &advices[0];
                        let b = main_gate.sub_sub_with_constant(
                            &mut ctx,
                            a,
                            a,
                            a,
                            M::Scalar::from(2),
                        )?;
                        let cond = main_gate.assign_bit(&mut ctx, Value::known(M::Scalar::ONE))?;
                        main_gate.select(&mut ctx, a, &b, &cond)?;

                        Ok(advices)
                    },
                )?;

                for (offset, advice) in advices.into_iter().enumerate() {
                    main_gate.expose_public(layouter.namespace(|| ""), advice, offset)?
                }

                Ok(())
            }
        }
    }
}
