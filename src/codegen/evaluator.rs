use crate::{codegen::util::Data, fe_to_u256};
use halo2_proofs::{
    halo2curves::ff::PrimeField,
    plonk::{
        Advice, AdviceQuery, Any, Challenge, ConstraintSystem, Expression, Fixed, FixedQuery, Gate,
        InstanceQuery,
    },
};
use itertools::{chain, izip, Itertools};
use ruint::aliases::U256;
use std::{borrow::Borrow, cell::RefCell, cmp::Ordering, collections::HashMap, iter};

#[derive(Debug)]
pub(crate) struct Evaluator<'a, F: PrimeField> {
    cs: &'a ConstraintSystem<F>,
    data: &'a Data,
    var_counter: RefCell<usize>,
    var_cache: RefCell<HashMap<String, String>>,
}

impl<'a, F> Evaluator<'a, F>
where
    F: PrimeField<Repr = [u8; 0x20]>,
{
    pub(crate) fn new(cs: &'a ConstraintSystem<F>, data: &'a Data) -> Self {
        Self {
            cs,
            data,
            var_counter: Default::default(),
            var_cache: Default::default(),
        }
    }

    pub fn gate_computations(&self) -> Vec<(Vec<String>, String)> {
        self.cs
            .gates()
            .iter()
            .flat_map(Gate::polynomials)
            .map(|expression| self.evaluate_and_reset(expression))
            .collect()
    }

    pub fn permutation_computations(&self) -> Vec<(Vec<String>, String)> {
        let permutation_columns = self.cs.permutation().get_columns();
        let permutation_chunk_len = self.cs.degree() - 2;
        let num_permutation_zs = permutation_columns.chunks(permutation_chunk_len).count();

        chain![
            self.data.permutation_z_evals.first().map(|evals| {
                vec![
                    "let l_0 := mload(L_0_MPTR)".to_string(),
                    format!("let perm_z_0 := {}", evals.0),
                    "let eval := addmod(l_0, sub(r, mulmod(l_0, perm_z_0, r)), r)".to_string(),
                ]
            }),
            self.data.permutation_z_evals.last().map(|evals| {
                let item = "addmod(mulmod(perm_z_last, perm_z_last, r), sub(r, perm_z_last), r)";
                vec![
                    "let l_last := mload(L_LAST_MPTR)".to_string(),
                    format!("let perm_z_last := {}", evals.0),
                    format!("let eval := mulmod(l_last, {item}, r)"),
                ]
            }),
            izip!(
                &self.data.permutation_z_evals,
                &self.data.permutation_z_evals[1..]
            )
            .map(|(evals, evals_next)| {
                vec![
                    "let l_0 := mload(L_0_MPTR)".to_string(),
                    format!("let perm_z_i_last := {}", evals.2),
                    format!("let perm_z_j := {}", evals_next.0),
                    "let eval := mulmod(l_0, addmod(perm_z_j, sub(r, perm_z_i_last), r), r)"
                        .to_string(),
                ]
            }),
            izip!(
                permutation_columns.chunks(permutation_chunk_len),
                &self.data.permutation_z_evals,
            )
            .enumerate()
            .map(|(chunk_idx, (columns, evals))| {
                chain![
                    [
                        "let gamma := mload(GAMMA_MPTR)".to_string(),
                        format!("let left := {}", evals.1),
                        format!("let right := {}", evals.0),
                        "let tmp".to_string(),
                    ],
                    columns.iter().flat_map(|column| {
                        let item = format!(
                            "mulmod(mload(BETA_MPTR), {}, r)",
                            self.data.permutation_evals[column],
                        );
                        [
                            format!(
                                "tmp := addmod(addmod({}, {item}, r), gamma, r)",
                                self.eval(*column.column_type(), column.index(), 0),
                            ),
                            "left := mulmod(left, tmp, r)".to_string(),
                        ]
                    }),
                    columns.iter().enumerate().flat_map(|(idx, column)| {
                        chain![
                            (chunk_idx == 0 && idx == 0).then(|| {
                                "mstore(0x00, mulmod(mload(BETA_MPTR), mload(X_MPTR), r))"
                                    .to_string()
                            }),
                            [
                                format!(
                                    "tmp := addmod(addmod({}, mload(0x00), r), gamma, r)",
                                    self.eval(*column.column_type(), column.index(), 0),
                                ),
                                "right := mulmod(right, tmp, r)".to_string(),
                            ],
                            (!(chunk_idx == num_permutation_zs - 1 && idx == columns.len() - 1))
                                .then(|| "mstore(0x00, mulmod(mload(0x00), delta, r))".to_string()),
                        ]
                    }),
                    {
                        let item = "sub(r, mulmod(left_sub_right, addmod(l_last, l_blind, r), r))";
                        [
                            "let l_blind := mload(L_BLIND_MPTR)".to_string(),
                            "let l_last := mload(L_LAST_MPTR)".to_string(),
                            "let left_sub_right := addmod(left, sub(r, right), r)".to_string(),
                            format!("let eval := addmod(left_sub_right, {item}, r)"),
                        ]
                    }
                ]
                .collect_vec()
            })
        ]
        .zip(iter::repeat("eval".to_string()))
        .collect()
    }

    pub fn lookup_computations(&self) -> Vec<(Vec<String>, String)> {
        let input_tables = self
            .cs
            .lookups()
            .iter()
            .map(|lookup| {
                let (input_lines, inputs) = lookup
                    .input_expressions()
                    .iter()
                    .map(|expression| self.evaluate(expression))
                    .fold((Vec::new(), Vec::new()), |mut acc, result| {
                        acc.0.extend(result.0);
                        acc.1.push(result.1);
                        acc
                    });
                self.reset();
                let (table_lines, tables) = lookup
                    .table_expressions()
                    .iter()
                    .map(|expression| self.evaluate(expression))
                    .fold((Vec::new(), Vec::new()), |mut acc, result| {
                        acc.0.extend(result.0);
                        acc.1.push(result.1);
                        acc
                    });
                self.reset();
                (input_lines, inputs, table_lines, tables)
            })
            .collect_vec();
        izip!(input_tables, &self.data.lookup_evals)
            .flat_map(|((input_lines, inputs, table_lines, tables), evals)| {
                [
                    vec![
                        "let l_0 := mload(L_0_MPTR)".to_string(),
                        format!(
                            "let eval := addmod(l_0, mulmod(l_0, sub(r, {}), r), r)",
                            evals.0
                        ),
                    ],
                    {
                        let item = format!(
                            "addmod(mulmod({}, {}, r), sub(r, {}), r)",
                            evals.0, evals.0, evals.0
                        );
                        vec![
                            "let l_last := mload(L_LAST_MPTR)".to_string(),
                            format!("let eval := mulmod(l_last, {item}, r)"),
                        ]
                    },
                    chain![
                        [
                            "let theta := mload(THETA_MPTR)",
                            "let beta := mload(BETA_MPTR)",
                            "let gamma := mload(GAMMA_MPTR)",
                            "let input",
                            "{"
                        ]
                        .map(str::to_string),
                        chain![
                            input_lines,
                            [format!("input := {}", &inputs[0])],
                            inputs[1..].iter().flat_map(|input| [
                                "input := mulmod(input, theta, r)".to_string(),
                                format!("input := addmod(input, {input}, r)"),
                            ])
                        ]
                        .map(|line| format!("    {line}")),
                        ["}".to_string()],
                        ["let table", "{"].map(str::to_string),
                        chain![
                            table_lines,
                            [format!("table := {}", &tables[0])],
                            tables[1..].iter().flat_map(|table| [
                                "table := mulmod(table, theta, r)".to_string(),
                                format!("table := addmod(table, {table}, r)"),
                            ])
                        ]
                        .map(|line| format!("    {line}")),
                        ["}".to_string()],
                        {
                            let permuted = format!(
                                "mulmod(addmod({}, beta, r), addmod({}, gamma, r), r)",
                                evals.2, evals.4
                            );
                            let input =
                                "mulmod(addmod(input, beta, r), addmod(table, gamma, r), r)";
                            [
                                format!("let left := mulmod({}, {permuted}, r)", evals.1),
                                format!("let right := mulmod({}, {input}, r)", evals.0),
                            ]
                        },
                        [
                            "let l_blind := mload(L_BLIND_MPTR)",
                            "let l_last := mload(L_LAST_MPTR)",
                            "let l_active := addmod(1, sub(r, addmod(l_last, l_blind, r)), r)",
                            "let eval := mulmod(l_active, addmod(left, sub(r, right), r), r)"
                        ]
                        .map(str::to_string),
                    ]
                    .collect_vec(),
                    vec![
                        "let l_0 := mload(L_0_MPTR)".to_string(),
                        format!(
                            "let eval := mulmod(l_0, addmod({}, sub(r, {}), r), r)",
                            evals.2, evals.4
                        ),
                    ],
                    vec![
                        "let l_blind := mload(L_BLIND_MPTR)".to_string(),
                        "let l_last := mload(L_LAST_MPTR)".to_string(),
                        "let l_active := addmod(1, sub(r, addmod(l_last, l_blind, r)), r)"
                            .to_string(),
                        format!("let eval := l_active"),
                        format!(
                            "eval := mulmod(eval, addmod({}, sub(r, {}), r), r)",
                            evals.2, evals.4
                        ),
                        format!(
                            "eval := mulmod(eval, addmod({}, sub(r, {}), r), r)",
                            evals.2, evals.3
                        ),
                    ],
                ]
            })
            .zip(iter::repeat("eval".to_string()))
            .collect_vec()
    }

    fn eval(&self, column_type: impl Into<Any>, column_index: usize, rotation: i32) -> String {
        match column_type.into() {
            Any::Advice(_) => self.data.advice_evals[&(column_index, rotation)].to_string(),
            Any::Fixed => self.data.fixed_evals[&(column_index, rotation)].to_string(),
            Any::Instance => self.data.instance_eval.to_string(),
        }
    }

    fn reset(&self) {
        *self.var_counter.borrow_mut() = Default::default();
        *self.var_cache.borrow_mut() = Default::default();
    }

    fn evaluate_and_reset(&self, expression: &Expression<F>) -> (Vec<String>, String) {
        let result = self.evaluate(expression);
        self.reset();
        result
    }

    fn evaluate(&self, expression: &Expression<F>) -> (Vec<String>, String) {
        evaluate(
            expression,
            &|constant| {
                let constant = u256_string(constant);
                self.init_var(constant, None)
            },
            &|query| {
                self.init_var(
                    self.eval(Fixed, query.column_index(), query.rotation().0),
                    Some(fixed_eval_var(query)),
                )
            },
            &|query| {
                self.init_var(
                    self.eval(Advice::default(), query.column_index(), query.rotation().0),
                    Some(advice_eval_var(query)),
                )
            },
            &|_| self.init_var(&self.data.instance_eval, Some("i_eval".to_string())),
            &|challenge| {
                self.init_var(
                    &self.data.challenges[challenge.index()],
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
                let scalar = u256_string(scalar);
                let (lines, var) = self.init_var(format!("mulmod({var}, {scalar}, r)"), None);
                acc.extend(lines);
                (acc, var)
            },
        )
    }

    fn init_var(&self, value: impl ToString, var: Option<String>) -> (Vec<String>, String) {
        let value = value.to_string();
        if self.var_cache.borrow().contains_key(&value) {
            (vec![], self.var_cache.borrow()[&value].clone())
        } else {
            let var = var.unwrap_or_else(|| self.next_var());
            self.var_cache
                .borrow_mut()
                .insert(value.clone(), var.clone());
            (vec![format!("let {var} := {value}")], var)
        }
    }

    fn next_var(&self) -> String {
        let count = *self.var_counter.borrow();
        *self.var_counter.borrow_mut() += 1;
        format!("var{count}")
    }
}

fn u256_string(value: U256) -> String {
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
