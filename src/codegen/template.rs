use crate::codegen::{
    pcs::BatchOpenScheme::{self, Bdfg21, Gwc19},
    util::Ptr,
};
use askama::{Error, Template};
use ruint::aliases::U256;
use std::fmt;

#[derive(Template)]
#[template(path = "Halo2VerifyingKey.sol")]
pub(crate) struct Halo2VerifyingKey {
    pub(crate) constants: Vec<(&'static str, U256)>,
    pub(crate) fixed_comms: Vec<(U256, U256)>,
    pub(crate) permutation_comms: Vec<(U256, U256)>,
}

impl Halo2VerifyingKey {
    pub(crate) fn len(&self) -> usize {
        (self.constants.len() * 0x20)
            + (self.fixed_comms.len() + self.permutation_comms.len()) * 0x40
    }
}

#[derive(Template)]
#[template(path = "Halo2Verifier.sol")]
pub(crate) struct Halo2Verifier {
    pub(crate) scheme: BatchOpenScheme,
    pub(crate) vk: Option<Halo2VerifyingKey>,
    pub(crate) vk_len: usize,
    pub(crate) proof_len: usize,
    pub(crate) vk_mptr: Ptr,
    pub(crate) challenge_mptr: Ptr,
    pub(crate) theta_mptr: Ptr,
    pub(crate) proof_cptr: Ptr,
    pub(crate) quotient_comm_cptr: Ptr,
    pub(crate) num_neg_lagranges: usize,
    pub(crate) num_advices: Vec<usize>,
    pub(crate) num_challenges: Vec<usize>,
    pub(crate) num_evals: usize,
    pub(crate) num_quotients: usize,
    pub(crate) quotient_eval_numer_computations: Vec<Vec<String>>,
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
        Ok(if value.len() % 2 == 1 {
            format!("0x0{value}")
        } else {
            format!("0x{value}")
        })
    }

    pub fn hex_padded(value: impl LowerHex, pad: usize) -> ::askama::Result<String> {
        let string = format!("0x{value:0pad$x}");
        if string == "0x0" {
            Ok(format!("0x{}", "0".repeat(pad)))
        } else {
            Ok(string)
        }
    }
}
