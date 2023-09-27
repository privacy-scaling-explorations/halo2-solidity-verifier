use crate::codegen::{
    template::Halo2VerifyingKey,
    BatchOpenScheme::{self, Bdfg21, Gwc19},
};
use halo2_proofs::{
    halo2curves::{bn256, ff::PrimeField, CurveAffine},
    plonk::{Any, Column, ConstraintSystem},
};
use itertools::{chain, izip, Itertools};
use ruint::{aliases::U256, UintTryFrom};
use std::{
    borrow::Borrow,
    collections::HashMap,
    fmt::{self, Display, Formatter},
    ops::{Add, Sub},
};

#[derive(Debug)]
pub(crate) struct ConstraintSystemMeta {
    pub(crate) num_fixeds: usize,
    pub(crate) permutation_columns: Vec<Column<Any>>,
    pub(crate) permutation_chunk_len: usize,
    pub(crate) num_lookup_permuteds: usize,
    pub(crate) num_permutation_zs: usize,
    pub(crate) num_lookup_zs: usize,
    pub(crate) num_quotients: usize,
    pub(crate) advice_queries: Vec<(usize, i32)>,
    pub(crate) fixed_queries: Vec<(usize, i32)>,
    pub(crate) num_evals: usize,
    pub(crate) num_user_advices: Vec<usize>,
    pub(crate) num_user_challenges: Vec<usize>,
    pub(crate) advice_indices: Vec<usize>,
    pub(crate) challenge_indices: Vec<usize>,
    pub(crate) rotation_last: i32,
}

impl ConstraintSystemMeta {
    pub(crate) fn new(cs: &ConstraintSystem<impl PrimeField>) -> Self {
        let num_fixeds = cs.num_fixed_columns();
        let permutation_columns = cs.permutation().get_columns();
        let permutation_chunk_len = cs.degree() - 2;
        let num_lookup_permuteds = 2 * cs.lookups().len();
        let num_permutation_zs = cs
            .permutation()
            .get_columns()
            .chunks(cs.degree() - 2)
            .count();
        let num_lookup_zs = cs.lookups().len();
        let num_quotients = cs.degree() - 1;
        let advice_queries = cs
            .advice_queries()
            .iter()
            .map(|(column, rotation)| (column.index(), rotation.0))
            .collect_vec();
        let fixed_queries = cs
            .fixed_queries()
            .iter()
            .map(|(column, rotation)| (column.index(), rotation.0))
            .collect_vec();
        let num_evals = advice_queries.len()
            + fixed_queries.len()
            + 1
            + cs.permutation().get_columns().len()
            + (3 * num_permutation_zs - 1)
            + 5 * cs.lookups().len();
        let num_phase = *cs.advice_column_phase().iter().max().unwrap_or(&0) as usize + 1;
        // Indices of advice and challenge are not same as their position in calldata/memory,
        // because we support multiple phases, we need to remap them and find their actual indices.
        let remapping = |phase: Vec<u8>| {
            let nums = phase.iter().fold(vec![0; num_phase], |mut nums, phase| {
                nums[*phase as usize] += 1;
                nums
            });
            let offsets = nums
                .iter()
                .take(num_phase - 1)
                .fold(vec![0], |mut offsets, n| {
                    offsets.push(offsets.last().unwrap() + n);
                    offsets
                });
            let index = phase
                .iter()
                .scan(offsets, |state, phase| {
                    let index = state[*phase as usize];
                    state[*phase as usize] += 1;
                    Some(index)
                })
                .collect::<Vec<_>>();
            (nums, index)
        };
        let (num_user_advices, advice_indices) = remapping(cs.advice_column_phase());
        let (num_user_challenges, challenge_indices) = remapping(cs.challenge_phase());
        let rotation_last = -(cs.blinding_factors() as i32 + 1);
        Self {
            num_fixeds,
            permutation_columns,
            permutation_chunk_len,
            num_lookup_permuteds,
            num_permutation_zs,
            num_lookup_zs,
            num_quotients,
            advice_queries,
            fixed_queries,
            num_evals,
            num_user_advices,
            num_user_challenges,
            advice_indices,
            challenge_indices,
            rotation_last,
        }
    }

    pub(crate) fn num_advices(&self) -> Vec<usize> {
        chain![
            self.num_user_advices.iter().cloned(),
            (self.num_lookup_permuteds != 0).then_some(self.num_lookup_permuteds), // lookup permuted
            [
                self.num_permutation_zs + self.num_lookup_zs + 1, // permutation and lookup grand products, random
                self.num_quotients,                               // quotients
            ],
        ]
        .collect()
    }

    pub(crate) fn num_challenges(&self) -> Vec<usize> {
        let mut num_challenges = self.num_user_challenges.clone();
        // If there is no lookup used, merge also beta and gamma into the last user phase, to avoid
        // squeezing challenge from nothing.
        // Otherwise, merge theta into last user phase since they are originally adjacent.
        if self.num_lookup_permuteds == 0 {
            *num_challenges.last_mut().unwrap() += 3; // theta, beta, gamma
            num_challenges.extend([
                1, // y
                1, // x
            ]);
        } else {
            *num_challenges.last_mut().unwrap() += 1; // theta
            num_challenges.extend([
                2, // beta, gamma
                1, // y
                1, // x
            ]);
        }
        num_challenges
    }

    pub(crate) fn num_permutations(&self) -> usize {
        self.permutation_columns.len()
    }

    pub(crate) fn num_lookups(&self) -> usize {
        self.num_lookup_zs
    }

    pub(crate) fn proof_len(&self, scheme: BatchOpenScheme) -> usize {
        self.num_advices().iter().sum::<usize>() * 0x40
            + self.num_evals * 0x20
            + self.batch_open_proof_len(scheme)
    }

    pub(crate) fn batch_open_proof_len(&self, scheme: BatchOpenScheme) -> usize {
        match scheme {
            Bdfg21 => 2 * 0x40,
            Gwc19 => {
                unimplemented!()
            }
        }
    }
}

#[derive(Debug)]
pub(crate) struct Data {
    pub(crate) challenge_mptr: Ptr,
    pub(crate) theta_mptr: Ptr,

    pub(crate) quotient_comm_cptr: Ptr,
    pub(crate) w_cptr: Ptr,

    pub(crate) fixed_comms: Vec<EcPoint>,
    pub(crate) permutation_comms: HashMap<Column<Any>, EcPoint>,
    pub(crate) advice_comms: Vec<EcPoint>,
    pub(crate) lookup_permuted_comms: Vec<(EcPoint, EcPoint)>,
    pub(crate) permutation_z_comms: Vec<EcPoint>,
    pub(crate) lookup_z_comms: Vec<EcPoint>,
    pub(crate) random_comm: EcPoint,

    pub(crate) challenges: Vec<Word>,

    pub(crate) instance_eval: Word,
    pub(crate) advice_evals: HashMap<(usize, i32), Word>,
    pub(crate) fixed_evals: HashMap<(usize, i32), Word>,
    pub(crate) random_eval: Word,
    pub(crate) permutation_evals: HashMap<Column<Any>, Word>,
    pub(crate) permutation_z_evals: Vec<(Word, Word, Word)>,
    pub(crate) lookup_evals: Vec<(Word, Word, Word, Word, Word)>,

    pub(crate) computed_quotient_comm: EcPoint,
    pub(crate) computed_quotient_eval: Word,
}

impl Data {
    pub(crate) fn new(
        meta: &ConstraintSystemMeta,
        vk: &Halo2VerifyingKey,
        vk_mptr: Ptr,
        proof_cptr: Ptr,
    ) -> Self {
        let fixed_comm_mptr = vk_mptr + vk.constants.len();
        let permutation_comm_mptr = fixed_comm_mptr + 2 * vk.fixed_comms.len();
        let challenge_mptr = permutation_comm_mptr + 2 * vk.permutation_comms.len();
        let theta_mptr = challenge_mptr + meta.challenge_indices.len();

        let advice_comm_start = proof_cptr;
        let lookup_permuted_comm_start = advice_comm_start + 2 * meta.advice_indices.len();
        let permutation_z_comm_start = lookup_permuted_comm_start + 2 * meta.num_lookup_permuteds;
        let lookup_z_comm_start = permutation_z_comm_start + 2 * meta.num_permutation_zs;
        let random_comm_start = lookup_z_comm_start + 2 * meta.num_lookup_zs;
        let quotient_comm_start = random_comm_start + 2;

        let eval_cptr = quotient_comm_start + 2 * meta.num_quotients;
        let advice_eval_cptr = eval_cptr;
        let fixed_eval_cptr = advice_eval_cptr + meta.advice_queries.len();
        let random_eval_cptr = fixed_eval_cptr + meta.fixed_queries.len();
        let permutation_eval_cptr = random_eval_cptr + 1;
        let permutation_z_eval_cptr = permutation_eval_cptr + meta.num_permutations();
        let lookup_eval_cptr = permutation_z_eval_cptr + 3 * meta.num_permutation_zs - 1;
        let w_cptr = lookup_eval_cptr + 5 * meta.num_lookups();

        let fixed_comms = EcPoint::range(fixed_comm_mptr)
            .take(meta.num_fixeds)
            .collect();
        let permutation_comms = izip!(
            meta.permutation_columns.iter().cloned(),
            EcPoint::range(permutation_comm_mptr)
        )
        .collect();
        let advice_comms = meta
            .advice_indices
            .iter()
            .map(|idx| advice_comm_start + 2 * idx)
            .map_into()
            .collect();
        let lookup_permuted_comms = EcPoint::range(lookup_permuted_comm_start)
            .take(meta.num_lookup_permuteds)
            .tuples()
            .collect();
        let permutation_z_comms = EcPoint::range(permutation_z_comm_start)
            .take(meta.num_permutation_zs)
            .collect();
        let lookup_z_comms = EcPoint::range(lookup_z_comm_start)
            .take(meta.num_lookup_zs)
            .collect();
        let random_comm = random_comm_start.into();
        let computed_quotient_comm = EcPoint::new(
            Ptr::memory("QUOTIENT_X_MPTR"),
            Ptr::memory("QUOTIENT_Y_MPTR"),
        );

        let challenges = meta
            .challenge_indices
            .iter()
            .map(|idx| challenge_mptr + *idx)
            .map_into()
            .collect_vec();
        let instance_eval = Ptr::memory("INSTANCE_EVAL_MPTR").into();
        let advice_evals = izip!(
            meta.advice_queries.iter().cloned(),
            Word::range(advice_eval_cptr)
        )
        .collect();
        let fixed_evals = izip!(
            meta.fixed_queries.iter().cloned(),
            Word::range(fixed_eval_cptr)
        )
        .collect();
        let random_eval = random_eval_cptr.into();
        let permutation_evals = izip!(
            meta.permutation_columns.iter().cloned(),
            Word::range(permutation_eval_cptr)
        )
        .collect();
        let permutation_z_evals = Word::range(permutation_z_eval_cptr)
            .take(3 * meta.num_permutation_zs)
            .tuples()
            .collect_vec();
        let lookup_evals = Word::range(lookup_eval_cptr)
            .take(5 * meta.num_lookup_zs)
            .tuples()
            .collect_vec();
        let computed_quotient_eval = Ptr::memory("QUOTIENT_EVAL_MPTR").into();

        Self {
            challenge_mptr,
            theta_mptr,
            quotient_comm_cptr: quotient_comm_start,
            w_cptr,

            fixed_comms,
            permutation_comms,
            advice_comms,
            lookup_permuted_comms,
            permutation_z_comms,
            lookup_z_comms,
            random_comm,
            computed_quotient_comm,

            challenges,

            instance_eval,
            advice_evals,
            fixed_evals,
            permutation_evals,
            permutation_z_evals,
            lookup_evals,
            random_eval,
            computed_quotient_eval,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Location {
    Calldata,
    Memory,
}

impl Location {
    fn opcode(&self) -> &'static str {
        match self {
            Location::Calldata => "calldataload",
            Location::Memory => "mload",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Value {
    Integer(usize),
    Identifier(&'static str),
}

impl Value {
    pub(crate) fn is_integer(&self) -> bool {
        match self {
            Value::Integer(_) => true,
            Value::Identifier(_) => false,
        }
    }

    pub(crate) fn as_usize(&self) -> usize {
        match self {
            Value::Integer(int) => *int,
            Value::Identifier(_) => unreachable!(),
        }
    }
}

impl Default for Value {
    fn default() -> Self {
        Self::Integer(0)
    }
}

impl From<&'static str> for Value {
    fn from(ident: &'static str) -> Self {
        Value::Identifier(ident)
    }
}

impl From<usize> for Value {
    fn from(int: usize) -> Self {
        Value::Integer(int)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Value::Integer(int) => {
                let hex = format!("{int:x}");
                if hex.len() % 2 == 1 {
                    write!(f, "0x0{hex}")
                } else {
                    write!(f, "0x{hex}")
                }
            }
            Value::Identifier(ident) => {
                write!(f, "{ident}")
            }
        }
    }
}

impl Add<usize> for Value {
    type Output = Value;

    fn add(self, rhs: usize) -> Self::Output {
        (self.as_usize() + rhs * 0x20).into()
    }
}

impl Sub<usize> for Value {
    type Output = Value;

    fn sub(self, rhs: usize) -> Self::Output {
        (self.as_usize() - rhs * 0x20).into()
    }
}

/// `Ptr` points to a EVM word at either calldata or memory.
///
/// When adding or subtracting it by 1, its value moves by 32 and points to next/previous EVM word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Ptr {
    loc: Location,
    value: Value,
}

impl Ptr {
    pub(crate) fn new(loc: Location, value: impl Into<Value>) -> Self {
        Self {
            loc,
            value: value.into(),
        }
    }

    pub(crate) fn memory(value: impl Into<Value>) -> Self {
        Self::new(Location::Memory, value.into())
    }

    pub(crate) fn calldata(value: impl Into<Value>) -> Self {
        Self::new(Location::Calldata, value.into())
    }

    pub(crate) fn loc(&self) -> Location {
        self.loc
    }

    pub(crate) fn value(&self) -> Value {
        self.value
    }
}

impl Display for Ptr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Add<usize> for Ptr {
    type Output = Ptr;

    fn add(mut self, rhs: usize) -> Self::Output {
        self.value = self.value + rhs;
        self
    }
}

impl Sub<usize> for Ptr {
    type Output = Ptr;

    fn sub(mut self, rhs: usize) -> Self::Output {
        self.value = self.value - rhs;
        self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Word(Ptr);

impl Word {
    pub(crate) fn range(word: impl Into<Word>) -> impl Iterator<Item = Word> {
        let ptr = word.into().ptr();
        (0..).map(move |idx| ptr + idx).map_into()
    }

    pub(crate) fn ptr(&self) -> Ptr {
        self.0
    }
}

impl Display for Word {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}({})", self.0.loc.opcode(), self.0.value)
    }
}

impl From<Ptr> for Word {
    fn from(ptr: Ptr) -> Self {
        Self(ptr)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct EcPoint {
    x: Word,
    y: Word,
}

impl EcPoint {
    pub(crate) fn new(x: impl Into<Word>, y: impl Into<Word>) -> Self {
        Self {
            x: x.into(),
            y: y.into(),
        }
    }

    pub(crate) fn range(ec_point: impl Into<EcPoint>) -> impl Iterator<Item = EcPoint> {
        let ptr = ec_point.into().x.ptr();
        (0..).map(move |idx| ptr + 2 * idx).map_into()
    }

    pub(crate) fn loc(&self) -> Location {
        self.x.ptr().loc()
    }

    pub(crate) fn x(&self) -> Word {
        self.x
    }

    pub(crate) fn y(&self) -> Word {
        self.y
    }
}

impl From<Ptr> for EcPoint {
    fn from(ptr: Ptr) -> Self {
        Self::new(ptr, ptr + 1)
    }
}

/// Add indention to given lines by `4 * N` spaces.
pub(crate) fn indent<const N: usize>(lines: impl IntoIterator<Item = String>) -> Vec<String> {
    lines
        .into_iter()
        .map(|line| format!("{}{line}", " ".repeat(N * 4)))
        .collect()
}

/// Create a code block for given lines with indention.
///
/// If `PACKED` is true, single line code block will be packed into single line.
pub(crate) fn code_block<const N: usize, const PACKED: bool>(
    lines: impl IntoIterator<Item = String>,
) -> Vec<String> {
    let lines = lines.into_iter().collect_vec();
    let bracket_indent = " ".repeat((N - 1) * 4);
    match lines.len() {
        0 => vec![format!("{bracket_indent}{{}}")],
        1 if PACKED => vec![format!("{bracket_indent}{{ {} }}", lines[0])],
        _ => chain![
            [format!("{bracket_indent}{{")],
            indent::<N>(lines),
            [format!("{bracket_indent}}}")],
        ]
        .collect(),
    }
}

/// Create a for loop with proper indention.
pub(crate) fn for_loop(
    initialization: impl IntoIterator<Item = String>,
    condition: impl Into<String>,
    advancement: impl IntoIterator<Item = String>,
    body: impl IntoIterator<Item = String>,
) -> Vec<String> {
    chain![
        ["for".to_string()],
        code_block::<2, true>(initialization),
        indent::<1>([condition.into()]),
        code_block::<2, true>(advancement),
        code_block::<1, false>(body),
    ]
    .collect()
}

pub(crate) fn g1_to_u256s(ec_point: impl Borrow<bn256::G1Affine>) -> [U256; 2] {
    let coords = ec_point.borrow().coordinates().unwrap();
    [coords.x(), coords.y()].map(fq_to_u256)
}

pub(crate) fn g2_to_u256s(ec_point: impl Borrow<bn256::G2Affine>) -> [U256; 4] {
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

pub(crate) fn fq_to_u256(fe: impl Borrow<bn256::Fq>) -> U256 {
    fe_to_u256(fe)
}

pub(crate) fn fr_to_u256(fe: impl Borrow<bn256::Fr>) -> U256 {
    fe_to_u256(fe)
}

pub(crate) fn fe_to_u256<F>(fe: impl Borrow<F>) -> U256
where
    F: PrimeField<Repr = [u8; 0x20]>,
{
    U256::from_le_bytes(fe.borrow().to_repr())
}

pub(crate) fn to_u256_be_bytes<T>(value: T) -> [u8; 32]
where
    U256: UintTryFrom<T>,
{
    U256::from(value).to_be_bytes()
}
