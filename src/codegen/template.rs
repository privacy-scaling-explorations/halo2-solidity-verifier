use askama::{Error, Template};
use ruint::aliases::U256;
use std::fmt;

#[derive(Template)]
#[template(path = "Halo2VerifyingKey.sol")]
pub(crate) struct Halo2VerifyingKey {
    pub(crate) constants: Vec<(&'static str, U256)>,
    pub(crate) fixed_commitments: Vec<U256>,
    pub(crate) permutation_commitments: Vec<U256>,
}

impl Halo2VerifyingKey {
    pub(crate) fn len(&self) -> usize {
        (self.constants.len() + self.fixed_commitments.len() + self.permutation_commitments.len())
            * 0x20
    }
}

#[derive(Template)]
#[template(path = "Halo2Verifier.sol")]
pub(crate) struct Halo2Verifier {
    pub(crate) vk_mptr: usize,
    pub(crate) vk_len: usize,
    pub(crate) num_neg_lagranges: usize,
    pub(crate) num_witnesses: Vec<usize>,
    pub(crate) num_challenges: Vec<usize>,
    pub(crate) num_evals: usize,
    pub(crate) num_quotients: usize,
    pub(crate) quotient_cptr: usize,
    pub(crate) proof_len: usize,
    pub(crate) challenge_mptr: usize,
    pub(crate) theta_mptr: usize,
    pub(crate) instance_eval_mptr: usize,
    pub(crate) expression_computations: Vec<Vec<String>>,
    pub(crate) pcs_computations: Vec<Vec<String>>,
}

impl Halo2VerifyingKey {
    pub(crate) fn render(&self, writer: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        self.render_into(writer).map_err(|err| match err {
            Error::Fmt(err) => err,
            _ => unreachable!(),
        })
    }
}

impl Halo2Verifier {
    pub(crate) fn render(&self, writer: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        self.render_into(writer).map_err(|err| match err {
            Error::Fmt(err) => err,
            _ => unreachable!(),
        })
    }
}

mod filters {
    use std::fmt::LowerHex;

    pub fn hex(value: impl LowerHex) -> ::askama::Result<String> {
        let value = format!("{value:x}");
        Ok(if value == "0" {
            format!("0x{}", "0".repeat(64))
        } else if value.len() % 2 == 1 {
            format!("0x0{value}")
        } else {
            format!("0x{value}")
        })
    }

    pub fn hex_padded(value: impl LowerHex, pad: usize) -> ::askama::Result<String> {
        Ok(format!("0x{value:0pad$x}", pad = pad))
    }
}
