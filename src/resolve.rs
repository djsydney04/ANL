use crate::{
    MAX_DEPTH,
    diagnostic::{Diagnostic, Sources, Span},
    syntax,
    types::{Expr, ExprKind, Function, Program, Type, UnaryOp},
};
use std::collections::HashMap;

struct Signature {
    params: Vec<Type>,
    result: Type,
    span: Span,
    public: bool,
}
struct Binding {
    name: Option<String>,
    ty: Type,
    span: Span,
}
struct Checker {
    signatures: Vec<Signature>,
    names: Vec<HashMap<String, Member>>,
    current_module: usize,
    next_id: usize,
}

pub(crate) struct Module {
    pub functions: Vec<syntax::Function>,
    pub imports: Vec<Import>,
}
pub(crate) struct Import {
    pub name: String,
    pub target: usize,
    pub public: bool,
    pub span: Span,
}
#[derive(Clone, Copy)]
enum Member {
    Function(usize),
    Module {
        target: usize,
        public: bool,
        span: Span,
    },
}

pub fn check(modules: Vec<Module>, sources: Sources) -> Result<Program, Diagnostic> {
    let mut checker = Checker {
        signatures: Vec::new(),
        names: Vec::new(),
        current_module: 0,
        next_id: 0,
    };
    for module in &modules {
        let mut names = HashMap::new();
        for function in &module.functions {
            if let Some(Member::Function(id)) = names.insert(
                function.name.clone(),
                Member::Function(checker.signatures.len()),
            ) {
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
                public: function.public,
            });
        }
        for import in &module.imports {
            if let Some(previous) = names.insert(
                import.name.clone(),
                Member::Module {
                    target: import.target,
                    public: import.public,
                    span: import.span,
                },
            ) {
                let span = match previous {
                    Member::Function(id) => checker.signatures[id].span,
                    Member::Module { span, .. } => span,
                };
                return Err(Diagnostic::new(
                    import.span,
                    format!("duplicate name `{}` in module namespace", import.name),
                )
                .related(span, "previous declaration here"));
            }
        }
        checker.names.push(names);
    }
    let modular = modules.len() > 1;
    let mut checked = Vec::with_capacity(checker.signatures.len());
    for (module_id, module) in modules.into_iter().enumerate() {
        checker.current_module = module_id;
        for function in module.functions {
            let mut env = Vec::new();
            let mut parameter_names = HashMap::new();
            for parameter in function.params {
                if let Some(previous) =
                    parameter_names.insert(parameter.name.clone(), parameter.span)
                {
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
            let name = if modular && !(module_id == 0 && function.name == "main") {
                format!("__apl_m{module_id}_{}", function.name)
            } else {
                function.name
            };
            checked.push(Function {
                name,
                params: env.iter().map(|p| p.ty).collect(),
                result: function.result,
                body,
                span: function.span,
            });
        }
    }
    Ok(Program {
        functions: checked,
        sources,
    })
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
    fn function(&self, name: &str, span: Span) -> Result<usize, Diagnostic> {
        let mut parts = name.split("::").peekable();
        let mut module = self.current_module;
        let mut first = true;
        while let Some(part) = parts.next() {
            let member = self.names[module].get(part).copied();
            if parts.peek().is_some() {
                match member {
                    Some(Member::Module {
                        target,
                        public,
                        span: declaration,
                    }) => {
                        if !first && !public {
                            return Err(Diagnostic::new(
                                span,
                                format!("module `{part}` is private in path `{name}`"),
                            )
                            .related(
                                declaration,
                                "private module declared here; export it with pub mod",
                            ));
                        }
                        module = target;
                        first = false;
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            span,
                            format!("undefined module `{part}` in path `{name}`"),
                        ));
                    }
                }
            } else {
                return match member {
                    Some(Member::Function(id)) => {
                        let signature = &self.signatures[id];
                        if module != self.current_module && !signature.public {
                            Err(
                                Diagnostic::new(span, format!("function `{name}` is private"))
                                    .related(
                                        signature.span,
                                        "private function declared here; export it with pub fn",
                                    ),
                            )
                        } else {
                            Ok(id)
                        }
                    }
                    Some(Member::Module { .. }) => Err(Diagnostic::new(
                        span,
                        format!("module `{name}` is not a function or scalar value"),
                    )),
                    None => Err(Diagnostic::new(
                        span,
                        format!("undefined function `{name}`"),
                    )),
                };
            }
        }
        unreachable!("a source name always has at least one segment")
    }

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
                } else if name.contains("::") || self.names[self.current_module].contains_key(&name)
                {
                    self.function(&name, span)?;
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
                            source_id: span.source_id,
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
                let function = self.function(&name, span)?;
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
