use crate::{
    MAX_EVAL_DEPTH,
    diagnostic::Span,
    types::{BinaryOp, Expr, ExprKind, Program, Type, UnaryOp},
};
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value {
    Integer(i64),
    Boolean(bool),
    Unit,
}
impl Value {
    pub fn ty(self) -> Type {
        match self {
            Self::Integer(_) => Type::I64,
            Self::Boolean(_) => Type::Bool,
            Self::Unit => Type::Unit,
        }
    }
}
impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(n) => write!(f, "{n}"),
            Self::Boolean(b) => write!(f, "{b}"),
            Self::Unit => f.write_str("()"),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Trap {
    ArithmeticOverflow,
    DivisionByZero,
}
impl Trap {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ArithmeticOverflow => "arithmetic_overflow",
            Self::DivisionByZero => "division_by_zero",
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError {
    Trap { kind: Trap, span: Span },
    ResourceLimit { reason: &'static str, span: Span },
    InvalidIr,
}

pub fn evaluate(program: &Program, entry: usize, fuel: u64) -> Result<Value, EvalError> {
    let function = program.functions.get(entry).ok_or(EvalError::InvalidIr)?;
    if !function.params.is_empty() {
        return Err(EvalError::InvalidIr);
    }
    Evaluator { program, fuel }.expr(&function.body, &mut Vec::new(), 0)
}

struct Evaluator<'a> {
    program: &'a Program,
    fuel: u64,
}
impl Evaluator<'_> {
    fn expr(
        &mut self,
        expr: &Expr,
        env: &mut Vec<Value>,
        depth: usize,
    ) -> Result<Value, EvalError> {
        if depth >= MAX_EVAL_DEPTH {
            return Err(EvalError::ResourceLimit {
                reason: "evaluation nesting limit exceeded",
                span: expr.span,
            });
        }
        if self.fuel == 0 {
            return Err(EvalError::ResourceLimit {
                reason: "fuel exhausted",
                span: expr.span,
            });
        }
        self.fuel -= 1;
        let next = depth + 1;
        let value = match &expr.kind {
            ExprKind::Integer(n) => Value::Integer(*n),
            ExprKind::Boolean(b) => Value::Boolean(*b),
            ExprKind::Unit => Value::Unit,
            ExprKind::Local(index) => *env
                .get(
                    env.len()
                        .checked_sub(index.checked_add(1).ok_or(EvalError::InvalidIr)?)
                        .ok_or(EvalError::InvalidIr)?,
                )
                .ok_or(EvalError::InvalidIr)?,
            ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                let value = self.expr(value, env, next)?;
                env.push(value);
                let result = self.expr(body, env, next);
                env.pop();
                result?
            }
            ExprKind::Assign { index, value } => {
                let value = self.expr(value, env, next)?;
                let position = env
                    .len()
                    .checked_sub(index.checked_add(1).ok_or(EvalError::InvalidIr)?)
                    .ok_or(EvalError::InvalidIr)?;
                let target = env.get_mut(position).ok_or(EvalError::InvalidIr)?;
                if target.ty() != value.ty() {
                    return Err(EvalError::InvalidIr);
                }
                *target = value;
                Value::Unit
            }
            ExprKind::While { condition, body } => {
                loop {
                    match self.expr(condition, env, next)? {
                        Value::Boolean(false) => break,
                        Value::Boolean(true) => {
                            if self.expr(body, env, next)? != Value::Unit {
                                return Err(EvalError::InvalidIr);
                            }
                        }
                        _ => return Err(EvalError::InvalidIr),
                    }
                }
                Value::Unit
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let Value::Boolean(condition) = self.expr(condition, env, next)? else {
                    return Err(EvalError::InvalidIr);
                };
                self.expr(if condition { then_branch } else { else_branch }, env, next)?
            }
            ExprKind::Unary { op, operand } => {
                let value = self.expr(operand, env, next)?;
                match (op, value) {
                    (UnaryOp::Not, Value::Boolean(b)) => Value::Boolean(!b),
                    (UnaryOp::Neg, Value::Integer(n)) => {
                        Value::Integer(n.checked_neg().ok_or(EvalError::Trap {
                            kind: Trap::ArithmeticOverflow,
                            span: expr.span,
                        })?)
                    }
                    _ => return Err(EvalError::InvalidIr),
                }
            }
            ExprKind::Binary { op, left, right } => {
                let left = self.expr(left, env, next)?;
                if *op == BinaryOp::And && left == Value::Boolean(false) {
                    Value::Boolean(false)
                } else if *op == BinaryOp::Or && left == Value::Boolean(true) {
                    Value::Boolean(true)
                } else {
                    let right = self.expr(right, env, next)?;
                    binary(*op, left, right, expr.span)?
                }
            }
            ExprKind::Call {
                function,
                arguments,
            } => {
                let function = self
                    .program
                    .functions
                    .get(*function)
                    .ok_or(EvalError::InvalidIr)?;
                if function.params.len() != arguments.len() {
                    return Err(EvalError::InvalidIr);
                }
                let mut values = Vec::with_capacity(arguments.len());
                for (argument, expected) in arguments.iter().zip(&function.params) {
                    let value = self.expr(argument, env, next)?;
                    if value.ty() != *expected {
                        return Err(EvalError::InvalidIr);
                    }
                    values.push(value);
                }
                self.expr(&function.body, &mut values, next)?
            }
        };
        if value.ty() != expr.ty {
            return Err(EvalError::InvalidIr);
        }
        Ok(value)
    }
}

fn binary(op: BinaryOp, left: Value, right: Value, span: Span) -> Result<Value, EvalError> {
    let overflow = || EvalError::Trap {
        kind: Trap::ArithmeticOverflow,
        span,
    };
    match (op, left, right) {
        (BinaryOp::Eq, a, b) if a.ty() == b.ty() => Ok(Value::Boolean(a == b)),
        (BinaryOp::Ne, a, b) if a.ty() == b.ty() => Ok(Value::Boolean(a != b)),
        (BinaryOp::And, Value::Boolean(a), Value::Boolean(b)) => Ok(Value::Boolean(a && b)),
        (BinaryOp::Or, Value::Boolean(a), Value::Boolean(b)) => Ok(Value::Boolean(a || b)),
        (op, Value::Integer(a), Value::Integer(b)) => {
            let value = match op {
                BinaryOp::Add => Value::Integer(a.checked_add(b).ok_or_else(overflow)?),
                BinaryOp::Sub => Value::Integer(a.checked_sub(b).ok_or_else(overflow)?),
                BinaryOp::Mul => Value::Integer(a.checked_mul(b).ok_or_else(overflow)?),
                BinaryOp::Div | BinaryOp::Rem => {
                    if b == 0 {
                        return Err(EvalError::Trap {
                            kind: Trap::DivisionByZero,
                            span,
                        });
                    }
                    Value::Integer(
                        if op == BinaryOp::Div {
                            a.checked_div(b)
                        } else {
                            a.checked_rem(b)
                        }
                        .ok_or_else(overflow)?,
                    )
                }
                BinaryOp::Lt => Value::Boolean(a < b),
                BinaryOp::Le => Value::Boolean(a <= b),
                BinaryOp::Gt => Value::Boolean(a > b),
                BinaryOp::Ge => Value::Boolean(a >= b),
                _ => return Err(EvalError::InvalidIr),
            };
            Ok(value)
        }
        _ => Err(EvalError::InvalidIr),
    }
}
