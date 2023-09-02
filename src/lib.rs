use halo2_proofs::halo2curves::{bn256, ff::PrimeField, CurveAffine};
use itertools::chain;
use ruint::aliases::U256;
use std::borrow::Borrow;

mod codegen;
mod transcript;

pub use codegen::{BatchOpenScheme, SolidityGenerator};
pub use transcript::{ChallengeEvm, Keccak256Transcript};

pub const FN_SIG_VERIFY_PROOF: [u8; 4] = [0x1e, 0x8e, 0x1e, 0x13];
pub const FN_SIG_VERIFY_PROOF_WITH_VK_ADDRESS: [u8; 4] = [0xaf, 0x83, 0xa1, 0x8d];

#[cfg(test)]
mod test;

pub fn encode_calldata(
    vk_address: Option<[u8; 20]>,
    proof: &[u8],
    instances: &[bn256::Fr],
) -> Vec<u8> {
    let (fn_sig, offset) = if vk_address.is_some() {
        (FN_SIG_VERIFY_PROOF_WITH_VK_ADDRESS, 0x60)
    } else {
        (FN_SIG_VERIFY_PROOF, 0x40)
    };
    let vk_address = if let Some(vk_address) = vk_address {
        U256::try_from_be_slice(&vk_address)
            .unwrap()
            .to_be_bytes::<0x20>()
            .to_vec()
    } else {
        Vec::new()
    };
    let num_instances = instances.len();
    chain![
        fn_sig,
        vk_address,
        U256::from(offset).to_be_bytes::<0x20>(),
        U256::from(offset + 0x20 + proof.len()).to_be_bytes::<0x20>(),
        U256::from(proof.len()).to_be_bytes::<0x20>(),
        proof.iter().cloned(),
        U256::from(num_instances).to_be_bytes::<0x20>(),
        instances
            .iter()
            .flat_map(|instance| fe_to_u256::<bn256::Fr>(instance).to_be_bytes::<0x20>()),
    ]
    .collect()
}

fn fe_to_u256<F>(fe: impl Borrow<F>) -> U256
where
    F: PrimeField<Repr = [u8; 0x20]>,
{
    U256::from_le_bytes(fe.borrow().to_repr())
}

fn g1_to_u256s(ec_point: impl Borrow<bn256::G1Affine>) -> [U256; 2] {
    let coords = ec_point.borrow().coordinates().unwrap();
    [coords.x(), coords.y()].map(fe_to_u256::<bn256::Fq>)
}

fn g2_to_u256s(ec_point: impl Borrow<bn256::G2Affine>) -> [U256; 4] {
    let coords = ec_point.borrow().coordinates().unwrap();
    let x = coords.x().to_repr();
    let y = coords.y().to_repr();
    [
        U256::try_from_le_slice(&x.as_ref()[0x20..]).unwrap(),
        U256::try_from_le_slice(&x.as_ref()[..0x20]).unwrap(),
        U256::try_from_le_slice(&y.as_ref()[0x20..]).unwrap(),
        U256::try_from_le_slice(&y.as_ref()[..0x20]).unwrap(),
    ]
}
