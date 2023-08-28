use crate::{
    codegen::{calldataload_asm, mload_asm},
    fe_to_u256,
};
use halo2_proofs::{
    halo2curves::ff::PrimeField,
    plonk::{
        AdviceQuery, Any, Challenge, Column, ConstraintSystem, Expression, FixedQuery,
        InstanceQuery,
    },
};
use itertools::{izip, Itertools};
use ruint::aliases::U256;
use std::{borrow::Borrow, cell::RefCell, cmp::Ordering, collections::HashMap};

#[derive(Debug)]
pub struct ExpressionEvaluator {
    challenge_asm: Vec<String>,
    pub instance_eval_asm: String,
    pub l_last_asm: String,
    pub l_blind_asm: String,
    pub l_0_asm: String,
    pub advice_eval_asm: HashMap<(usize, i32), String>,
    pub fixed_eval_asm: HashMap<(usize, i32), String>,
    pub random_eval_asm: String,
    pub permutation_eval_asm: HashMap<Column<Any>, String>,
    pub permutation_z_eval_asm: Vec<(String, String, String)>,
    pub lookup_eval_asm: Vec<(String, String, String, String, String)>,
    var_counter: RefCell<usize>,
    var_cache: RefCell<HashMap<String, String>>,
}

impl ExpressionEvaluator {
    pub fn new<F: PrimeField>(
        cs: &ConstraintSystem<F>,
        challenge_mptr: usize,
        mut eval_cptr: usize,
    ) -> Self {
        let challenge_asm = (challenge_mptr..)
            .step_by(0x20)
            .take(cs.num_challenges())
            .map(mload_asm)
            .collect_vec();

        let num_permutation_zs = cs
            .permutation()
            .get_columns()
            .chunks(cs.degree() - 2)
            .count();
        let advice_queries = cs.advice_queries().clone();
        let fixed_queries = cs.fixed_queries().clone();

        let instance_eval_asm = "mload(INSTANCE_EVAL_MPTR)".to_string();
        let l_last_asm = "mload(L_LAST_MPTR)".to_string();
        let l_blind_asm = "mload(L_BLIND_MPTR)".to_string();
        let l_0_asm = "mload(L_0_MPTR)".to_string();

        let advice_eval_asm = izip!(
            advice_queries
                .iter()
                .map(|(column, rotation)| (column.index(), rotation.0)),
            (eval_cptr..).step_by(0x20).map(calldataload_asm)
        )
        .collect::<HashMap<_, _>>();
        eval_cptr += advice_queries.len() * 0x20;

        let fixed_eval_asm = izip!(
            fixed_queries
                .iter()
                .map(|(column, rotation)| (column.index(), rotation.0)),
            (eval_cptr..).step_by(0x20).map(calldataload_asm)
        )
        .collect::<HashMap<_, _>>();
        eval_cptr += fixed_queries.len() * 0x20;

        let random_eval_asm = calldataload_asm(eval_cptr);
        eval_cptr += 0x20;

        let permutation_eval_asm = cs
            .permutation()
            .get_columns()
            .into_iter()
            .zip((eval_cptr..).step_by(0x20).map(calldataload_asm))
            .collect();
        eval_cptr += cs.permutation().get_columns().len() * 0x20;

        let permutation_z_eval_asm = (eval_cptr..)
            .step_by(0x20)
            .map(calldataload_asm)
            .take(3 * num_permutation_zs)
            .tuples()
            .collect_vec();
        eval_cptr += (3 * num_permutation_zs - 1) * 0x20;

        let lookup_eval_asm = (eval_cptr..)
            .step_by(0x20)
            .map(calldataload_asm)
            .take(5 * cs.lookups().len())
            .tuples()
            .collect_vec();

        Self {
            challenge_asm,
            instance_eval_asm,
            l_last_asm,
            l_blind_asm,
            l_0_asm,
            advice_eval_asm,
            fixed_eval_asm,
            random_eval_asm,
            permutation_eval_asm,
            permutation_z_eval_asm,
            lookup_eval_asm,
            var_counter: Default::default(),
            var_cache: Default::default(),
        }
    }

    pub fn eval_asm(&self, column: &Column<Any>) -> String {
        match column.column_type() {
            Any::Advice(_) => self.advice_eval_asm[&(column.index(), 0)].clone(),
            Any::Fixed => self.fixed_eval_asm[&(column.index(), 0)].clone(),
            Any::Instance => self.instance_eval_asm.clone(),
        }
    }

    pub fn reset(&mut self) {
        self.var_counter = Default::default();
        self.var_cache = Default::default();
    }

    pub fn evaluate_and_reset<F>(&mut self, expression: &Expression<F>) -> (Vec<String>, String)
    where
        F: PrimeField<Repr = [u8; 0x20]>,
    {
        let result = self.evaluate(expression);
        self.reset();
        result
    }

    pub fn evaluate<F>(&mut self, expression: &Expression<F>) -> (Vec<String>, String)
    where
        F: PrimeField<Repr = [u8; 0x20]>,
    {
        evaluate(
            expression,
            &|constant| {
                let constant = u256_asm(constant);
                self.init_var(constant, None)
            },
            &|fixed_query| {
                self.init_var(
                    self.fixed_eval_asm[&(fixed_query.column_index(), fixed_query.rotation().0)]
                        .clone(),
                    Some(fixed_eval_var(fixed_query)),
                )
            },
            &|advice_query| {
                self.init_var(
                    self.advice_eval_asm[&(advice_query.column_index(), advice_query.rotation().0)]
                        .clone(),
                    Some(advice_eval_var(advice_query)),
                )
            },
            &|_| {
                self.init_var(
                    self.instance_eval_asm.clone(),
                    Some("instance_eval".to_string()),
                )
            },
            &|challenge| {
                self.init_var(
                    self.challenge_asm[challenge.index()].clone(),
                    Some(format!("c_{}", challenge.index())),
                )
            },
            &|(mut acc, var)| {
                let (lines, var) = self.init_var(format!("sub(r, {var})"), None);
                acc.extend(lines);
                (acc, var)
            },
            &|(mut lhs_acc, lhs_var), (rhs_acc, rhs_var)| {
                let (lines, var) = self.init_var(format!("addmod({lhs_var}, {rhs_var}, r)"), None);
                lhs_acc.extend(rhs_acc);
                lhs_acc.extend(lines);
                (lhs_acc, var)
            },
            &|(mut lhs_acc, lhs_var), (rhs_acc, rhs_var)| {
                let (lines, var) = self.init_var(format!("mulmod({lhs_var}, {rhs_var}, r)"), None);
                lhs_acc.extend(rhs_acc);
                lhs_acc.extend(lines);
                (lhs_acc, var)
            },
            &|(mut acc, var), scalar| {
                let scalar = u256_asm(scalar);
                let (lines, var) = self.init_var(format!("mulmod({var}, {scalar}, r)"), None);
                acc.extend(lines);
                (acc, var)
            },
        )
    }

    fn init_var(&self, asm: String, var: Option<String>) -> (Vec<String>, String) {
        if self.var_cache.borrow().contains_key(&asm) {
            (vec![], self.var_cache.borrow()[&asm].clone())
        } else {
            let var = var.unwrap_or_else(|| self.next_var());
            self.var_cache.borrow_mut().insert(asm.clone(), var.clone());
            (vec![format!("let {var} := {asm}")], var)
        }
    }

    fn next_var(&self) -> String {
        let count = *self.var_counter.borrow();
        *self.var_counter.borrow_mut() += 1;
        format!("var{count}")
    }
}

fn u256_asm(value: U256) -> String {
    if value.bit_len() < 64 {
        format!("0x{:x}", value.as_limbs()[0])
    } else {
        format!("0x{value:x}")
    }
}

fn fixed_eval_var(fixed_query: FixedQuery) -> String {
    let column_index = fixed_query.column_index();
    let rotation = fixed_query.rotation().0;
    match rotation.cmp(&0) {
        Ordering::Less => {
            format!("f_{}_rot_neg_{}", column_index, rotation.abs())
        }
        Ordering::Equal => {
            format!("f_{}", column_index)
        }
        Ordering::Greater => {
            format!("f_{}_rot_{}", column_index, rotation)
        }
    }
}

fn advice_eval_var(advice_query: AdviceQuery) -> String {
    let column_index = advice_query.column_index();
    let rotation = advice_query.rotation().0;
    match rotation.cmp(&0) {
        Ordering::Less => {
            format!("a_{}_rot_neg_{}", column_index, rotation.abs())
        }
        Ordering::Equal => {
            format!("a_{}", column_index)
        }
        Ordering::Greater => {
            format!("a_{}_rot_{}", column_index, rotation)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn evaluate<F, T>(
    expression: &Expression<F>,
    constant: &impl Fn(U256) -> T,
    fixed: &impl Fn(FixedQuery) -> T,
    advice: &impl Fn(AdviceQuery) -> T,
    instance: &impl Fn(InstanceQuery) -> T,
    challenge: &impl Fn(Challenge) -> T,
    negated: &impl Fn(T) -> T,
    sum: &impl Fn(T, T) -> T,
    product: &impl Fn(T, T) -> T,
    scaled: &impl Fn(T, U256) -> T,
) -> T
where
    F: PrimeField<Repr = [u8; 0x20]>,
{
    let evaluate = |expr| {
        evaluate(
            expr, constant, fixed, advice, instance, challenge, negated, sum, product, scaled,
        )
    };
    match expression.borrow() {
        Expression::Constant(scalar) => constant(fe_to_u256(*scalar)),
        Expression::Selector(_) => unreachable!(),
        Expression::Fixed(query) => fixed(*query),
        Expression::Advice(query) => advice(*query),
        Expression::Instance(query) => instance(*query),
        Expression::Challenge(value) => challenge(*value),
        Expression::Negated(value) => negated(evaluate(value)),
        Expression::Sum(lhs, rhs) => sum(evaluate(lhs), evaluate(rhs)),
        Expression::Product(lhs, rhs) => product(evaluate(lhs), evaluate(rhs)),
        Expression::Scaled(value, scalar) => scaled(evaluate(value), fe_to_u256(*scalar)),
    }
}
