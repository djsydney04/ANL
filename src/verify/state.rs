//! Loop-free symbolic execution with scalar snapshots and lexical mutable cells.
use super::{
    Failure,
    formula::{Generator, Id, Pending, Symbolic, sort},
};
use crate::types::{BinaryOp, Expr, ExprKind, Type};

#[derive(Clone, Copy)]
struct Binding {
    value: Id,
    ty: Type,
    mutable: bool,
}

impl Generator<'_> {
    fn copy_state(&mut self, env: &[Binding]) -> Result<Vec<Binding>, Failure> {
        self.arena.work(env.len())?;
        let mut copy = Vec::with_capacity(env.len());
        for cell in env {
            self.arena.work(0)?;
            copy.push(*cell);
        }
        Ok(copy)
    }

    fn entry_state(&mut self, values: &[Id], types: &[Type]) -> Result<Vec<Binding>, Failure> {
        if values.len() != types.len() {
            return Err(Failure::Error("symbolic call arity mismatch".into()));
        }
        self.arena.work(values.len())?;
        let mut env = Vec::with_capacity(values.len());
        for (value, ty) in values.iter().zip(types) {
            self.arena.work(0)?;
            env.push(Binding {
                value: *value,
                ty: *ty,
                mutable: false,
            });
        }
        Ok(env)
    }

    fn merge_state(
        &mut self,
        env: &mut [Binding],
        other: &[Binding],
        condition: Id,
        true_is_env: bool,
    ) -> Result<(), Failure> {
        if env.len() != other.len() {
            return Err(Failure::Error("symbolic branch scope mismatch".into()));
        }
        self.arena.work(env.len())?;
        for (cell, alternative) in env.iter_mut().zip(other) {
            self.arena.work(0)?;
            if cell.ty != alternative.ty || cell.mutable != alternative.mutable {
                return Err(Failure::Error("symbolic branch binding mismatch".into()));
            }
            if cell.value != alternative.value {
                let (yes, no) = if true_is_env {
                    (cell.value, alternative.value)
                } else {
                    (alternative.value, cell.value)
                };
                cell.value = self
                    .arena
                    .add(sort(cell.ty)?, format!("(ite n{condition} n{yes} n{no})"))?;
            }
        }
        Ok(())
    }

    fn state_expr(
        &mut self,
        expr: &Expr,
        env: &mut Vec<Binding>,
        depth: usize,
    ) -> Result<Symbolic, Failure> {
        self.visit(depth)?;
        let safe = self.arena.truth()?;
        Ok(match &expr.kind {
            ExprKind::Tuple(_) | ExprKind::Project { .. } => {
                return Err(Failure::Unsupported(
                    "flat products are outside scalar verification".into(),
                ));
            }
            ExprKind::Integer(n) => Symbolic {
                value: self.arena.int(&if *n < 0 {
                    format!("(- {})", n.unsigned_abs())
                } else {
                    n.to_string()
                })?,
                safe,
            },
            ExprKind::Boolean(b) => Symbolic {
                value: self.arena.bool(*b)?,
                safe,
            },
            ExprKind::Unit => Symbolic {
                value: self.arena.int("0")?,
                safe,
            },
            ExprKind::Local(index) => {
                self.arena.work(1)?;
                let cell = env
                    .len()
                    .checked_sub(index + 1)
                    .and_then(|i| env.get(i))
                    .ok_or_else(|| Failure::Error("invalid checked local".into()))?;
                Symbolic {
                    value: cell.value,
                    safe,
                }
            }
            ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                let initial = self.state_expr(value, env, depth + 1)?;
                self.arena.work(1)?;
                env.push(Binding {
                    value: initial.value,
                    ty: value.ty,
                    mutable: matches!(expr.kind, ExprKind::LetMut { .. }),
                });
                let result = self.state_expr(body, env, depth + 1)?;
                self.arena.work(1)?;
                env.pop();
                Symbolic {
                    value: result.value,
                    safe: self.arena.and(&[initial.safe, result.safe])?,
                }
            }
            ExprKind::Assign { index, value } => {
                let result = self.state_expr(value, env, depth + 1)?;
                self.arena.work(1)?;
                let target = env
                    .len()
                    .checked_sub(index + 1)
                    .and_then(|i| env.get_mut(i))
                    .ok_or_else(|| Failure::Error("invalid checked assignment".into()))?;
                if !target.mutable || target.ty != value.ty {
                    return Err(Failure::Error(
                        "invalid checked assignment permission or type".into(),
                    ));
                }
                target.value = result.value;
                Symbolic {
                    value: self.arena.int("0")?,
                    safe: result.safe,
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let c = self.state_expr(condition, env, depth + 1)?;
                let mut yes_env = self.copy_state(env)?;
                let yes = self.state_expr(then_branch, &mut yes_env, depth + 1)?;
                let no = self.state_expr(else_branch, env, depth + 1)?;
                self.merge_state(env, &yes_env, c.value, false)?;
                let yes_safe = self.arena.implies(c.value, yes.safe)?;
                let not_condition = self.arena.not(c.value)?;
                let no_safe = self.arena.implies(not_condition, no.safe)?;
                Symbolic {
                    value: self.arena.add(
                        sort(expr.ty)?,
                        format!("(ite n{} n{} n{})", c.value, yes.value, no.value),
                    )?,
                    safe: self.arena.and(&[c.safe, yes_safe, no_safe])?,
                }
            }
            ExprKind::Unary { op, operand } => {
                let value = self.state_expr(operand, env, depth + 1)?;
                self.unary(*op, value, true)?
            }
            ExprKind::Binary { op, left, right } => {
                let a = self.state_expr(left, env, depth + 1)?;
                if matches!(op, BinaryOp::And | BinaryOp::Or) {
                    let skipped = self.copy_state(env)?;
                    let b = self.state_expr(right, env, depth + 1)?;
                    self.merge_state(env, &skipped, a.value, *op == BinaryOp::And)?;
                    self.binary(*op, a, b, expr.ty, true)?
                } else {
                    let b = self.state_expr(right, env, depth + 1)?;
                    self.binary(*op, a, b, expr.ty, true)?
                }
            }
            ExprKind::Call {
                function,
                arguments,
            } => {
                self.arena.work(arguments.len() * 2)?;
                let mut values = Vec::with_capacity(arguments.len());
                let mut conditions = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    let value = self.state_expr(argument, env, depth + 1)?;
                    values.push(value.value);
                    conditions.push(value.safe);
                }
                let contracts = self
                    .program
                    .contracts
                    .as_ref()
                    .ok_or_else(|| Failure::Error("source contracts are absent".into()))?;
                for clause in &contracts[*function].requires {
                    let pre = self.spec(&clause.expr, &values, None, depth + 1)?;
                    self.arena.work(2)?;
                    conditions.extend([pre.safe, pre.value]);
                }
                let callee = &self.program.functions[*function];
                let mut callee_env = self.entry_state(&values, &callee.params)?;
                let result = self.state_expr(&callee.body, &mut callee_env, depth + 1)?;
                self.arena.work(1)?;
                conditions.push(result.safe);
                Symbolic {
                    value: result.value,
                    safe: self.arena.and(&conditions)?,
                }
            }
            ExprKind::While { .. } => {
                return Err(Failure::Unsupported(
                    "loops are outside apl-state-verify-v1".into(),
                ));
            }
        })
    }
}

pub(super) fn obligations(
    genr: &mut Generator<'_>,
    function: usize,
) -> Result<Vec<Pending>, Failure> {
    let f = &genr.program.functions[function];
    let contract = &genr
        .program
        .contracts
        .as_ref()
        .ok_or_else(|| Failure::Error("missing source contracts".into()))?[function];
    let (params, domain) = genr.parameters(&f.params)?;
    let mut assumptions = domain;
    let mut pending = Vec::new();
    for clause in &contract.requires {
        let p = genr.spec(&clause.expr, &params, None, 0)?;
        let not_defined = genr.arena.not(p.safe)?;
        let assertion = genr.arena.and(&[assumptions, not_defined])?;
        pending.push(Pending {
            kind: "precondition_defined",
            span: clause.span,
            assertion,
            expected_sat: false,
        });
        assumptions = genr.arena.and(&[assumptions, p.safe, p.value])?;
    }
    pending.push(Pending {
        kind: "precondition_satisfiable",
        span: f.span,
        assertion: assumptions,
        expected_sat: true,
    });
    let mut env = genr.entry_state(&params, &f.params)?;
    let body = genr.state_expr(&f.body, &mut env, 0)?;
    let unsafe_body = genr.arena.not(body.safe)?;
    let assertion = genr.arena.and(&[assumptions, unsafe_body])?;
    pending.push(Pending {
        kind: "body_safe",
        span: f.body.span,
        assertion,
        expected_sat: false,
    });
    for clause in &contract.ensures {
        let p = genr.spec(&clause.expr, &params, Some(body.value), 0)?;
        let property = genr.arena.and(&[body.safe, p.safe, p.value])?;
        let neg = genr.arena.not(property)?;
        let assertion = genr.arena.and(&[assumptions, neg])?;
        pending.push(Pending {
            kind: "postcondition",
            span: clause.span,
            assertion,
            expected_sat: false,
        });
    }
    Ok(pending)
}
