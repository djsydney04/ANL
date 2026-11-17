use crate::{
    MAX_DEPTH,
    diagnostic::{Diagnostic, Span},
    syntax,
    types::{Expr, ExprKind, Function, Program, Type, UnaryOp},
};
use std::collections::HashMap;

struct Signature {
    params: Vec<Type>,
    result: Type,
    span: Span,
}
struct Binding {
    name: Option<String>,
    ty: Type,
    span: Span,
}
struct Checker {
    signatures: Vec<Signature>,
    names: HashMap<String, usize>,
    next_id: usize,
}

pub fn check(functions: Vec<syntax::Function>) -> Result<Program, Diagnostic> {
    let mut checker = Checker {
        signatures: Vec::new(),
        names: HashMap::new(),
        next_id: 0,
    };
    for function in &functions {
        if let Some(id) = checker
            .names
            .insert(function.name.clone(), checker.signatures.len())
        {
            return Err(Diagnostic::new(
                function.span,
                format!("duplicate function `{}`", function.name),
            )
            .related(
                checker.signatures[id].span,
                "previous function declared here",
            ));
        }
        checker.signatures.push(Signature {
            params: function.params.iter().map(|p| p.ty).collect(),
            result: function.result,
            span: function.span,
        });
    }
    let mut checked = Vec::with_capacity(functions.len());
    for function in functions {
        let mut env = Vec::new();
        let mut parameter_names = HashMap::new();
        for parameter in function.params {
            if let Some(previous) = parameter_names.insert(parameter.name.clone(), parameter.span) {
                return Err(Diagnostic::new(
                    parameter.span,
                    format!("duplicate parameter `{}`", parameter.name),
                )
                .related(previous, "previous parameter declared here"));
            }
            env.push(Binding {
                name: Some(parameter.name),
                ty: parameter.ty,
                span: parameter.span,
            });
        }
        let body = checker.expr(function.body, &mut env)?;
        expect_type(
            body.ty,
            function.result,
            body.span,
            function.result_span,
            "function result declared here",
        )?;
        checked.push(Function {
            name: function.name,
            params: env.iter().map(|p| p.ty).collect(),
            result: function.result,
            body,
            span: function.span,
        });
    }
    Ok(Program { functions: checked })
}

fn expect_type(
    actual: Type,
    expected: Type,
    span: Span,
    declaration: Span,
    note: &str,
) -> Result<(), Diagnostic> {
    if actual == expected {
        Ok(())
    } else {
        Err(
            Diagnostic::new(span, format!("expected {expected}, found {actual}"))
                .related(declaration, note),
        )
    }
}

impl Checker {
    fn node(
        &mut self,
        ty: Type,
        kind: ExprKind,
        span: Span,
        depth: usize,
    ) -> Result<Expr, Diagnostic> {
        if depth > MAX_DEPTH {
            return Err(Diagnostic::resource(
                span,
                "typed expression depth limit exceeded",
            ));
        }
        let id = self.next_id;
        self.next_id += 1;
        Ok(Expr {
            ty,
            kind,
            span,
            id,
            depth,
        })
    }
    fn expr(&mut self, expr: syntax::Expr, env: &mut Vec<Binding>) -> Result<Expr, Diagnostic> {
        let span = expr.span;
        let (ty, kind, depth) = match expr.kind {
            syntax::ExprKind::Integer(value) => {
                let value = value
                    .parse::<i64>()
                    .map_err(|_| Diagnostic::new(span, "integer literal is outside i64 range"))?;
                (Type::I64, ExprKind::Integer(value), 1)
            }
            syntax::ExprKind::Boolean(value) => (Type::Bool, ExprKind::Boolean(value), 1),
            syntax::ExprKind::Unit => (Type::Unit, ExprKind::Unit, 1),
            syntax::ExprKind::Name(name) => {
                let index = env
                    .iter()
                    .rposition(|binding| binding.name.as_ref() == Some(&name));
                if let Some(index) = index {
                    (env[index].ty, ExprKind::Local(env.len() - index - 1), 1)
                } else if self.names.contains_key(&name) {
                    return Err(Diagnostic::new(
                        span,
                        format!("function `{name}` cannot be used as a scalar value"),
                    ));
                } else {
                    return Err(Diagnostic::new(span, format!("undefined name `{name}`")));
                }
            }
            syntax::ExprKind::Group(inner) => return self.expr(*inner, env),
            syntax::ExprKind::Block { statements, tail } => {
                let outer = env.len();
                let mut names = HashMap::new();
                let mut initializers = Vec::new();
                for statement in statements {
                    match statement {
                        syntax::Statement::Let {
                            name,
                            span,
                            annotation,
                            value,
                        } => {
                            if let Some(previous) = names.insert(name.clone(), span) {
                                return Err(Diagnostic::new(
                                    span,
                                    format!("duplicate local binding `{name}` in this block"),
                                )
                                .related(previous, "previous binding declared here"));
                            }
                            let value = self.expr(value, env)?;
                            if let Some((expected, annotation_span)) = annotation {
                                expect_type(
                                    value.ty,
                                    expected,
                                    value.span,
                                    annotation_span,
                                    "local type declared here",
                                )?;
                            }
                            env.push(Binding {
                                name: Some(name),
                                ty: value.ty,
                                span,
                            });
                            initializers.push(value);
                        }
                        syntax::Statement::Discard(value) => {
                            let value = self.expr(value, env)?;
                            env.push(Binding {
                                name: None,
                                ty: value.ty,
                                span: value.span,
                            });
                            initializers.push(value);
                        }
                    }
                }
                let mut body = if let Some(tail) = tail {
                    self.expr(*tail, env)?
                } else {
                    self.node(
                        Type::Unit,
                        ExprKind::Unit,
                        Span {
                            start: span.end.saturating_sub(1),
                            end: span.end,
                        },
                        1,
                    )?
                };
                env.truncate(outer);
                for value in initializers.into_iter().rev() {
                    let depth = value.depth.max(body.depth) + 1;
                    body = self.node(
                        body.ty,
                        ExprKind::Let {
                            value: Box::new(value),
                            body: Box::new(body),
                        },
                        span,
                        depth,
                    )?;
                }
                return Ok(body);
            }
            syntax::ExprKind::Unary {
                op: UnaryOp::Neg,
                operand,
            } if matches!(operand.kind, syntax::ExprKind::Integer(_)) => {
                let syntax::ExprKind::Integer(magnitude) = operand.kind else {
                    unreachable!()
                };
                let magnitude = magnitude.parse::<u64>().map_err(|_| {
                    Diagnostic::new(span, "negative integer literal is outside i64 range")
                })?;
                let value = if magnitude == 1_u64 << 63 {
                    i64::MIN
                } else {
                    -i64::try_from(magnitude).map_err(|_| {
                        Diagnostic::new(span, "negative integer literal is outside i64 range")
                    })?
                };
                (Type::I64, ExprKind::Integer(value), 1)
            }
            syntax::ExprKind::Unary { op, operand } => {
                let operand = self.expr(*operand, env)?;
                expect_type(
                    operand.ty,
                    op.input(),
                    operand.span,
                    span,
                    "unary operator requires this type",
                )?;
                let depth = operand.depth + 1;
                (
                    op.input(),
                    ExprKind::Unary {
                        op,
                        operand: Box::new(operand),
                    },
                    depth,
                )
            }
            syntax::ExprKind::Binary { op, left, right } => {
                let left = self.expr(*left, env)?;
                let right = self.expr(*right, env)?;
                let ty = op.result(left.ty, right.ty).ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!(
                            "operator {} does not accept {} and {}",
                            op.as_str(),
                            left.ty,
                            right.ty
                        ),
                    )
                })?;
                let depth = left.depth.max(right.depth) + 1;
                (
                    ty,
                    ExprKind::Binary {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    depth,
                )
            }
            syntax::ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.expr(*condition, env)?;
                expect_type(
                    condition.ty,
                    Type::Bool,
                    condition.span,
                    span,
                    "if condition requires bool",
                )?;
                let then_branch = self.expr(*then_branch, env)?;
                let else_branch = self.expr(*else_branch, env)?;
                expect_type(
                    else_branch.ty,
                    then_branch.ty,
                    else_branch.span,
                    then_branch.span,
                    "other branch has this type",
                )?;
                let depth = 1 + condition
                    .depth
                    .max(then_branch.depth)
                    .max(else_branch.depth);
                (
                    then_branch.ty,
                    ExprKind::If {
                        condition: Box::new(condition),
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                    },
                    depth,
                )
            }
            syntax::ExprKind::Call { name, arguments } => {
                if let Some(binding) = env.iter().rev().find(|b| b.name.as_ref() == Some(&name)) {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "local `{name}` has type {} and cannot be called",
                            binding.ty
                        ),
                    )
                    .related(binding.span, "local declared here"));
                }
                let function = *self
                    .names
                    .get(&name)
                    .ok_or_else(|| Diagnostic::new(span, format!("undefined function `{name}`")))?;
                let signature = &self.signatures[function];
                if arguments.len() != signature.params.len() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "function `{name}` expects {} arguments, found {}",
                            signature.params.len(),
                            arguments.len()
                        ),
                    )
                    .related(signature.span, "function declared here"));
                }
                let params = signature.params.clone();
                let result = signature.result;
                let declaration = signature.span;
                let mut checked = Vec::new();
                let mut depth = 1;
                for (argument, expected) in arguments.into_iter().zip(params) {
                    let argument = self.expr(argument, env)?;
                    expect_type(
                        argument.ty,
                        expected,
                        argument.span,
                        declaration,
                        "parameter type declared here",
                    )?;
                    depth = depth.max(argument.depth + 1);
                    checked.push(argument);
                }
                (
                    result,
                    ExprKind::Call {
                        function,
                        arguments: checked,
                    },
                    depth,
                )
            }
        };
        self.node(ty, kind, span, depth)
    }
}
