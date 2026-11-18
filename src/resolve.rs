use crate::{
    MAX_DEPTH,
    diagnostic::{Diagnostic, Sources, Span},
    syntax,
    types::{
        BindingId, Clause, Expr, ExprKind, Function, FunctionContract, HeadBinding, LocalAssertion,
        LocalAssertionKind, LocalClause, LoopAnnotation, MemoryExpr, Program, ResourceMode,
        SpecExpr, SpecExprKind, SpecType, Type, UnaryOp, ViewMode,
    },
    word::WordValue,
};
use std::collections::{BTreeMap, HashMap};

struct Signature {
    view: Option<ViewMode>,
    params: Vec<Type>,
    result: Type,
    span: Span,
    public: bool,
}
struct Binding {
    order: usize,
    id: BindingId,
    name: Option<String>,
    ty: Type,
    mutable: bool,
    span: Span,
}
struct ResourceBinding {
    name: String,
    mode: ResourceMode,
    order: usize,
}
fn resource_shadows(name: &str, env: &[Binding], resources: &[ResourceBinding]) -> bool {
    let ordinary = env.iter().rev().find(|b| b.name.as_deref() == Some(name));
    let resource = resources.iter().rev().find(|b| b.name == name);
    resource.is_some_and(|r| ordinary.is_none_or(|b| r.order > b.order))
}
struct Checker {
    resources: Vec<ResourceBinding>,
    next_order: usize,
    next_site: usize,
    signatures: Vec<Signature>,
    names: Vec<HashMap<String, Member>>,
    current_module: usize,
    next_id: usize,
    bindings: Vec<HeadBinding>,
    loops: BTreeMap<usize, LoopAnnotation>,
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

pub(crate) struct ExternalSignature {
    pub name: String,
    pub params: Vec<Type>,
    pub result: Type,
}
pub(crate) struct CheckedFunctions {
    pub functions: Vec<Function>,
    pub contracts: Vec<FunctionContract>,
}

pub fn check(modules: Vec<Module>, sources: Sources) -> Result<Program, Diagnostic> {
    let checked = check_functions(modules, Vec::new())?;
    let mut program = Program {
        retained_revision: None,
        allocation_profile: None,
        functions: checked.functions,
        sources,
        contracts: Some(checked.contracts),
    };
    if program.has_memory() || program.uses_words() {
        program.allocation_profile =
            Some(crate::memory::AllocationProfile::host().map_err(|message| {
                let mut e = Diagnostic::new(Span::default(), message);
                e.infrastructure = true;
                e
            })?);
    }
    Ok(program)
}

pub(crate) fn check_functions(
    modules: Vec<Module>,
    external: Vec<ExternalSignature>,
) -> Result<CheckedFunctions, Diagnostic> {
    let mut checker = Checker {
        resources: Vec::new(),
        next_order: 0,
        next_site: 0,
        signatures: Vec::new(),
        names: Vec::new(),
        current_module: 0,
        next_id: 0,
        bindings: Vec::new(),
        loops: BTreeMap::new(),
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
                view: function.view.as_ref().map(|v| v.mode),
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
    for signature in external {
        let id = checker.signatures.len();
        if checker.names.len() != 1 || checker.names[0].contains_key(&signature.name) {
            return Err(Diagnostic::new(
                Span::default(),
                "invalid external signature namespace",
            ));
        }
        checker.names[0].insert(signature.name, Member::Function(id));
        checker.signatures.push(Signature {
            view: None,
            params: signature.params,
            result: signature.result,
            span: Span::default(),
            public: false,
        });
    }
    let modular = modules.len() > 1;
    let mut checked = Vec::with_capacity(checker.signatures.len());
    let mut contracts = Vec::with_capacity(checker.signatures.len());
    for (module_id, module) in modules.into_iter().enumerate() {
        checker.current_module = module_id;
        for function in module.functions {
            let mut env = Vec::new();
            let mut parameter_names = HashMap::new();
            checker.resources.clear();
            checker.next_site = 0;
            let view = function.view.as_ref().map(|v| v.mode);
            let view_name = function.view.as_ref().map(|v| v.name.clone());
            if let Some(v) = &function.view {
                parameter_names.insert(v.name.clone(), v.span);
                checker.push_resource(v.name.clone(), v.mode.into());
            }
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
                checker.push_binding(
                    &mut env,
                    Some(parameter.name),
                    parameter.ty,
                    false,
                    parameter.span,
                );
            }
            let requires = function
                .requires
                .into_iter()
                .map(|clause| spec_clause(clause, &env, None))
                .collect::<Result<Vec<_>, _>>()?;
            let mut ensures = Vec::new();
            for postcondition in function.ensures {
                if let Some(previous) = parameter_names.get(&postcondition.binder) {
                    return Err(Diagnostic::new(
                        postcondition.binder_span,
                        format!(
                            "result binder `{}` cannot shadow a parameter",
                            postcondition.binder
                        ),
                    )
                    .related(*previous, "parameter declared here"));
                }
                ensures.push(spec_clause(
                    postcondition.clause,
                    &env,
                    Some((&postcondition.binder, function.result)),
                )?);
            }
            let body = checker.expr(function.body, &mut env)?;
            let loops = std::mem::take(&mut checker.loops);
            let mut bindings = std::mem::take(&mut checker.bindings);
            if loops.is_empty() {
                bindings = Vec::new();
            }
            contracts.push(FunctionContract {
                view_name,
                source_name: function.name.clone(),
                param_names: env.iter().filter_map(|p| p.name.clone()).collect(),
                requires,
                ensures,
                bindings,
                loops,
            });
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
                view,
                name,
                params: env.iter().map(|p| p.ty).collect(),
                result: function.result,
                body,
                span: function.span,
            });
        }
    }
    Ok(CheckedFunctions {
        functions: checked,
        contracts,
    })
}

fn spec_type(ty: Type, span: Span) -> Result<SpecType, Diagnostic> {
    SpecType::from_type(ty).ok_or_else(|| {
        Diagnostic::new(
            span,
            "word-containing values are unsupported in specifications",
        )
    })
}

fn spec_clause(
    clause: syntax::Clause,
    params: &[Binding],
    result: Option<(&str, Type)>,
) -> Result<Clause, Diagnostic> {
    let expr = spec_expr(clause.expr, params, result)?;
    if expr.ty != SpecType::Bool {
        return Err(Diagnostic::new(
            expr.span,
            format!("contract clause must have type bool, found {}", expr.ty),
        ));
    }
    Ok(Clause {
        expr,
        span: clause.span,
    })
}

fn spec_expr(
    expr: syntax::Expr,
    params: &[Binding],
    result: Option<(&str, Type)>,
) -> Result<SpecExpr, Diagnostic> {
    let span = expr.span;
    let (ty, kind) = match expr.kind {
        syntax::ExprKind::Word(..) | syntax::ExprKind::Convert { .. } => {
            return Err(Diagnostic::new(
                span,
                "word syntax is unsupported in specifications",
            ));
        }
        syntax::ExprKind::Integer(value) => {
            let value = specification_integer(value, span)?;
            (SpecType::Int, SpecExprKind::Integer(value))
        }
        syntax::ExprKind::Boolean(value) => (SpecType::Bool, SpecExprKind::Boolean(value)),
        syntax::ExprKind::Unit => (SpecType::Unit, SpecExprKind::Unit),
        syntax::ExprKind::Name(name) => {
            if let Some((_, ty)) = result.filter(|(binder, _)| *binder == name) {
                (spec_type(ty, span)?, SpecExprKind::Result)
            } else if let Some(index) = params.iter().position(|p| p.name.as_ref() == Some(&name)) {
                (
                    spec_type(params[index].ty, span)?,
                    SpecExprKind::Param(index),
                )
            } else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "undefined specification name `{name}`; only parameters and this clause's result binder are available"
                    ),
                ));
            }
        }
        syntax::ExprKind::Group(inner) => return spec_expr(*inner, params, result),
        syntax::ExprKind::Unary { op, operand } => {
            let operand = spec_expr(*operand, params, result)?;
            let input = op.legacy_input().ok_or_else(|| {
                Diagnostic::new(span, "word operators are unsupported in specifications")
            })?;
            let ty = spec_type(input, span)?;
            if operand.ty != ty {
                return Err(Diagnostic::new(
                    operand.span,
                    format!(
                        "specification operator {} requires {ty}, found {}",
                        op.as_str(),
                        operand.ty
                    ),
                ));
            }
            (
                ty,
                SpecExprKind::Unary {
                    op,
                    operand: Box::new(operand),
                },
            )
        }
        syntax::ExprKind::Binary { op, left, right } => {
            if op.is_word() {
                return Err(Diagnostic::new(
                    span,
                    "word operators are unsupported in specifications",
                ));
            }
            let left = spec_expr(*left, params, result)?;
            let right = spec_expr(*right, params, result)?;
            // Runtime shapes are shared; specification integer values remain unbounded.
            let ty = op
                .result(left.ty.value_type(), right.ty.value_type())
                .ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!(
                            "specification operator {} does not accept {} and {}",
                            op.as_str(),
                            left.ty,
                            right.ty
                        ),
                    )
                })?;
            (
                spec_type(ty, span)?,
                SpecExprKind::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
            )
        }
        syntax::ExprKind::Tuple(fields) => {
            let fields = fields
                .into_iter()
                .map(|field| spec_expr(field, params, result))
                .collect::<Result<Vec<_>, _>>()?;
            let types = fields
                .iter()
                .map(|field| {
                    field.ty.value_type().scalar().ok_or_else(|| {
                        Diagnostic::new(field.span, "specification tuples must be flat")
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let shape = crate::types::TupleShape::new(&types)
                .map_err(|_| Diagnostic::new(span, "tuple requires 1..8 scalar fields"))?;
            (SpecType::Tuple(shape), SpecExprKind::Tuple(fields))
        }
        syntax::ExprKind::Project { value, index } => {
            let value = spec_expr(*value, params, result)?;
            let SpecType::Tuple(shape) = value.ty else {
                return Err(Diagnostic::new(span, "projection requires a tuple"));
            };
            let ty = shape
                .fields()
                .get(index)
                .ok_or_else(|| Diagnostic::new(span, "tuple projection index out of range"))?
                .as_type();
            (
                spec_type(ty, span)?,
                SpecExprKind::Project {
                    value: Box::new(value),
                    index,
                },
            )
        }
        syntax::ExprKind::Memory(_) => {
            return Err(Diagnostic::new(
                span,
                "buffers and views are not allowed in specifications",
            ));
        }
        syntax::ExprKind::Call { .. } => {
            return Err(Diagnostic::new(
                span,
                "function calls are not allowed in specification expressions",
            ));
        }
        syntax::ExprKind::Block { .. } => {
            return Err(Diagnostic::new(
                span,
                "blocks and local declarations are not allowed in specification expressions",
            ));
        }
        syntax::ExprKind::If { .. } => {
            return Err(Diagnostic::new(
                span,
                "conditional expressions are not allowed in specifications; use Boolean guards",
            ));
        }
    };
    Ok(SpecExpr { ty, span, kind })
}

fn specification_integer(value: String, span: Span) -> Result<String, Diagnostic> {
    if value.len() > 4096 {
        return Err(Diagnostic::resource(
            span,
            "specification integer literal exceeds 4096 decimal digits",
        ));
    }
    let digits = value.trim_start_matches('0');
    Ok(if digits.is_empty() { "0" } else { digits }.to_owned())
}

fn local_clause(
    clause: syntax::Clause,
    env: &[Binding],
    resources: &[ResourceBinding],
) -> Result<LocalClause, Diagnostic> {
    let expr = local_assertion(clause.expr, env, resources)?;
    if expr.ty != SpecType::Bool {
        return Err(Diagnostic::new(
            expr.span,
            format!("invariant clause must have type bool, found {}", expr.ty),
        ));
    }
    Ok(LocalClause {
        expr,
        span: clause.span,
    })
}

fn local_assertion(
    expr: syntax::Expr,
    env: &[Binding],
    resources: &[ResourceBinding],
) -> Result<LocalAssertion, Diagnostic> {
    let span = expr.span;
    let (ty, kind) = match expr.kind {
        syntax::ExprKind::Word(..) | syntax::ExprKind::Convert { .. } => {
            return Err(Diagnostic::new(
                span,
                "word syntax is unsupported in specifications",
            ));
        }
        syntax::ExprKind::Integer(value) => (
            SpecType::Int,
            LocalAssertionKind::Integer(specification_integer(value, span)?),
        ),
        syntax::ExprKind::Boolean(value) => (SpecType::Bool, LocalAssertionKind::Boolean(value)),
        syntax::ExprKind::Unit => (SpecType::Unit, LocalAssertionKind::Unit),
        syntax::ExprKind::Name(name) => {
            if resource_shadows(&name, env, resources) {
                return Err(Diagnostic::new(
                    span,
                    "resource names are not specification values",
                ));
            }
            let position = env.iter().rposition(|binding| binding.name.as_ref() == Some(&name))
                .ok_or_else(|| Diagnostic::new(span, format!(
                    "undefined invariant name `{name}`; only bindings visible at the loop head are available"
                )))?;
            (
                spec_type(env[position].ty, span)?,
                LocalAssertionKind::Local(env.len() - position - 1),
            )
        }
        syntax::ExprKind::Group(inner) => return local_assertion(*inner, env, resources),
        syntax::ExprKind::Unary { op, operand } => {
            let operand = local_assertion(*operand, env, resources)?;
            let input = op.legacy_input().ok_or_else(|| {
                Diagnostic::new(span, "word operators are unsupported in specifications")
            })?;
            let ty = spec_type(input, span)?;
            if operand.ty != ty {
                return Err(Diagnostic::new(
                    operand.span,
                    format!(
                        "specification operator {} requires {ty}, found {}",
                        op.as_str(),
                        operand.ty
                    ),
                ));
            }
            (
                ty,
                LocalAssertionKind::Unary {
                    op,
                    operand: Box::new(operand),
                },
            )
        }
        syntax::ExprKind::Binary { op, left, right } => {
            if op.is_word() {
                return Err(Diagnostic::new(
                    span,
                    "word operators are unsupported in specifications",
                ));
            }
            let left = local_assertion(*left, env, resources)?;
            let right = local_assertion(*right, env, resources)?;
            let ty = op
                .result(left.ty.value_type(), right.ty.value_type())
                .ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!(
                            "specification operator {} does not accept {} and {}",
                            op.as_str(),
                            left.ty,
                            right.ty
                        ),
                    )
                })?;
            (
                spec_type(ty, span)?,
                LocalAssertionKind::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
            )
        }
        syntax::ExprKind::Tuple(fields) => {
            let fields = fields
                .into_iter()
                .map(|field| local_assertion(field, env, resources))
                .collect::<Result<Vec<_>, _>>()?;
            let types = fields
                .iter()
                .map(|field| {
                    field.ty.value_type().scalar().ok_or_else(|| {
                        Diagnostic::new(field.span, "specification tuples must be flat")
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let shape = crate::types::TupleShape::new(&types)
                .map_err(|_| Diagnostic::new(span, "tuple requires 1..8 scalar fields"))?;
            (SpecType::Tuple(shape), LocalAssertionKind::Tuple(fields))
        }
        syntax::ExprKind::Project { value, index } => {
            let value = local_assertion(*value, env, resources)?;
            let SpecType::Tuple(shape) = value.ty else {
                return Err(Diagnostic::new(span, "projection requires a tuple"));
            };
            let ty = shape
                .fields()
                .get(index)
                .ok_or_else(|| Diagnostic::new(span, "tuple projection index out of range"))?
                .as_type();
            (
                spec_type(ty, span)?,
                LocalAssertionKind::Project {
                    value: Box::new(value),
                    index,
                },
            )
        }
        syntax::ExprKind::Memory(_) => {
            return Err(Diagnostic::new(
                span,
                "buffers and views are not allowed in specifications",
            ));
        }
        syntax::ExprKind::Call { .. } => {
            return Err(Diagnostic::new(
                span,
                "function calls are not allowed in invariant expressions",
            ));
        }
        syntax::ExprKind::Block { .. } => {
            return Err(Diagnostic::new(
                span,
                "blocks and local declarations are not allowed in invariant expressions",
            ));
        }
        syntax::ExprKind::If { .. } => {
            return Err(Diagnostic::new(
                span,
                "conditional expressions are not allowed in invariants; use Boolean guards",
            ));
        }
    };
    Ok(LocalAssertion { ty, span, kind })
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
    fn push_resource(&mut self, name: String, mode: ResourceMode) {
        let order = self.next_order;
        self.next_order += 1;
        self.resources.push(ResourceBinding { name, mode, order });
    }
    fn resource(
        &self,
        name: &str,
        env: &[Binding],
        span: Span,
    ) -> Result<(usize, ResourceMode), Diagnostic> {
        if !resource_shadows(name, env, &self.resources) {
            return Err(Diagnostic::new(
                span,
                format!("`{name}` is not a visible buffer"),
            ));
        }
        let position = self
            .resources
            .iter()
            .rposition(|r| r.name == name)
            .expect("visible resource");
        Ok((
            self.resources.len() - position - 1,
            self.resources[position].mode,
        ))
    }
    fn ordinary_name(&self, name: &str, env: &[Binding], span: Span) -> Result<(), Diagnostic> {
        if resource_shadows(name, env, &self.resources) {
            return Err(Diagnostic::new(
                span,
                format!("resource `{name}` cannot be used as a value or function"),
            ));
        }
        Ok(())
    }
    fn push_binding(
        &mut self,
        env: &mut Vec<Binding>,
        name: Option<String>,
        ty: Type,
        mutable: bool,
        span: Span,
    ) {
        let id = BindingId(self.bindings.len());
        self.bindings.push(HeadBinding {
            parent: env.last().map(|binding| binding.id),
            name: name.clone(),
            ty,
            mutable,
            span,
        });
        let order = self.next_order;
        self.next_order += 1;
        env.push(Binding {
            order,
            id,
            name,
            ty,
            mutable,
            span,
        });
    }

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
    fn memory(
        &mut self,
        memory: syntax::MemoryExpr,
        env: &mut Vec<Binding>,
        span: Span,
    ) -> Result<Expr, Diagnostic> {
        let kind = match memory {
            syntax::MemoryExpr::Heap {
                name,
                length,
                initial,
                success,
                failure,
            } => {
                let site = self.next_site;
                self.next_site += 1;
                let length = self.expr(*length, env)?;
                expect_type(
                    length.ty,
                    Type::I64,
                    length.span,
                    span,
                    "buffer length requires i64",
                )?;
                let initial = self.expr(*initial, env)?;
                expect_type(
                    initial.ty,
                    Type::I64,
                    initial.span,
                    span,
                    "buffer initializer requires i64",
                )?;
                self.push_resource(name, ResourceMode::Owner);
                let success = self.expr(*success, env);
                self.resources.pop();
                let success = success?;
                let failure = self.expr(*failure, env)?;
                expect_type(
                    failure.ty,
                    success.ty,
                    failure.span,
                    success.span,
                    "other heap branch has this type",
                )?;
                MemoryExpr::Heap {
                    site,
                    length: Box::new(length),
                    initial: Box::new(initial),
                    success: Box::new(success),
                    failure: Box::new(failure),
                }
            }
            syntax::MemoryExpr::Length { name } => MemoryExpr::Length {
                resource: self.resource(&name, env, span)?.0,
            },
            syntax::MemoryExpr::Read { name, index } => {
                let (resource, _) = self.resource(&name, env, span)?;
                let index = self.expr(*index, env)?;
                expect_type(
                    index.ty,
                    Type::I64,
                    index.span,
                    span,
                    "buffer index requires i64",
                )?;
                MemoryExpr::Read {
                    resource,
                    index: Box::new(index),
                }
            }
            syntax::MemoryExpr::Write { name, index, value } => {
                let (resource, mode) = self.resource(&name, env, span)?;
                if !mode.writable() {
                    return Err(Diagnostic::new(span, "read view cannot be written"));
                }
                let index = self.expr(*index, env)?;
                expect_type(
                    index.ty,
                    Type::I64,
                    index.span,
                    span,
                    "buffer index requires i64",
                )?;
                let value = self.expr(*value, env)?;
                expect_type(
                    value.ty,
                    Type::I64,
                    value.span,
                    span,
                    "buffer value requires i64",
                )?;
                MemoryExpr::Write {
                    resource,
                    index: Box::new(index),
                    value: Box::new(value),
                }
            }
            syntax::MemoryExpr::CallView {
                name,
                resource,
                mode,
                arguments,
            } => {
                self.ordinary_name(&name, env, span)?;
                if env.iter().any(|b| b.name.as_deref() == Some(&name)) {
                    return Err(Diagnostic::new(span, "local value cannot be called"));
                }
                let function = self.function(&name, span)?;
                let (resource, permission) = self.resource(&resource, env, span)?;
                if !permission.lends(mode) {
                    return Err(Diagnostic::new(
                        span,
                        "read view cannot lend edit permission",
                    ));
                }
                let sig = &self.signatures[function];
                if sig.view != Some(mode) || sig.params.len() != arguments.len() {
                    return Err(Diagnostic::new(span, "view call signature mismatch"));
                }
                let params = sig.params.clone();
                let mut checked = Vec::new();
                for (argument, expected) in arguments.into_iter().zip(params) {
                    let a = self.expr(argument, env)?;
                    expect_type(a.ty, expected, a.span, span, "argument type required here")?;
                    checked.push(a);
                }
                MemoryExpr::CallView {
                    function,
                    resource,
                    mode,
                    arguments: checked,
                }
            }
        };
        let ty = match &kind {
            MemoryExpr::Heap { success, .. } => success.ty,
            MemoryExpr::Write { .. } => Type::Unit,
            MemoryExpr::CallView { function, .. } => self.signatures[*function].result,
            _ => Type::I64,
        };
        let depth = 1 + kind.children().iter().map(|e| e.depth).max().unwrap_or(0);
        self.node(ty, ExprKind::Memory(Box::new(kind)), span, depth)
    }
    fn expr(&mut self, expr: syntax::Expr, env: &mut Vec<Binding>) -> Result<Expr, Diagnostic> {
        let span = expr.span;
        let (ty, kind, depth) = match expr.kind {
            syntax::ExprKind::Memory(memory) => return self.memory(*memory, env, span),
            syntax::ExprKind::Word(digits, width) => {
                let value = digits
                    .parse::<u64>()
                    .ok()
                    .and_then(|v| WordValue::new(width, v))
                    .ok_or_else(|| {
                        Diagnostic::new(span, "unsigned literal is outside its declared width")
                    })?;
                (Type::Word(width), ExprKind::Word(value), 1)
            }
            syntax::ExprKind::Convert {
                mode,
                target,
                operand,
            } => {
                let operand = self.expr(*operand, env)?;
                let ty = mode.result(operand.ty, target).ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        "conversion requires integer source and permitted destination",
                    )
                })?;
                let depth = operand.depth + 1;
                (
                    ty,
                    ExprKind::Convert {
                        mode,
                        target,
                        operand: Box::new(operand),
                    },
                    depth,
                )
            }
            syntax::ExprKind::Integer(value) => {
                let value = value
                    .parse::<i64>()
                    .map_err(|_| Diagnostic::new(span, "integer literal is outside i64 range"))?;
                (Type::I64, ExprKind::Integer(value), 1)
            }
            syntax::ExprKind::Tuple(fields) => {
                let mut checked = Vec::new();
                let mut shape = Vec::new();
                let mut depth = 1;
                for field in fields {
                    let field = self.expr(field, env)?;
                    shape.push(field.ty.scalar().ok_or_else(|| {
                        Diagnostic::new(field.span, "nested tuples are not supported")
                    })?);
                    depth = depth.max(field.depth + 1);
                    checked.push(field);
                }
                (
                    Type::Tuple(
                        crate::types::TupleShape::new(&shape)
                            .map_err(|e| Diagnostic::new(span, e.to_string()))?,
                    ),
                    ExprKind::Tuple(checked),
                    depth,
                )
            }
            syntax::ExprKind::Project { value, index } => {
                let value = self.expr(*value, env)?;
                let Type::Tuple(shape) = value.ty else {
                    return Err(Diagnostic::new(span, "projection requires a tuple"));
                };
                let ty = shape
                    .fields()
                    .get(index)
                    .ok_or_else(|| Diagnostic::new(span, "tuple projection index out of bounds"))?
                    .as_type();
                let depth = value.depth + 1;
                (
                    ty,
                    ExprKind::Project {
                        value: Box::new(value),
                        index,
                    },
                    depth,
                )
            }
            syntax::ExprKind::Boolean(value) => (Type::Bool, ExprKind::Boolean(value), 1),
            syntax::ExprKind::Unit => (Type::Unit, ExprKind::Unit, 1),
            syntax::ExprKind::Name(name) => {
                self.ordinary_name(&name, env, span)?;
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
                            mutable,
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
                            self.push_binding(env, Some(name), value.ty, mutable, span);
                            initializers.push((value, mutable));
                        }
                        syntax::Statement::Assign { name, span, value } => {
                            self.ordinary_name(&name, env, span)?;
                            let position = env
                                .iter()
                                .rposition(|binding| binding.name.as_ref() == Some(&name))
                                .ok_or_else(|| {
                                    Diagnostic::new(
                                        span,
                                        format!("undefined assignment target `{name}`"),
                                    )
                                })?;
                            let target = &env[position];
                            if !target.mutable {
                                return Err(Diagnostic::new(
                                    span,
                                    format!("cannot assign to immutable binding `{name}`"),
                                )
                                .related(target.span, "immutable binding declared here"));
                            }
                            let expected = target.ty;
                            let declaration = target.span;
                            let index = env.len() - position - 1;
                            let value = self.expr(value, env)?;
                            expect_type(
                                value.ty,
                                expected,
                                value.span,
                                declaration,
                                "assignment target declared here",
                            )?;
                            let expression_span = span.join(value.span);
                            let depth = value.depth + 1;
                            let value = self.node(
                                Type::Unit,
                                ExprKind::Assign {
                                    index,
                                    value: Box::new(value),
                                },
                                expression_span,
                                depth,
                            )?;
                            self.push_binding(env, None, Type::Unit, false, expression_span);
                            initializers.push((value, false));
                        }
                        syntax::Statement::While {
                            condition,
                            invariants,
                            body,
                            span,
                        } => {
                            let head = env.last().map(|binding| binding.id);
                            let clauses = invariants
                                .into_iter()
                                .map(|clause| local_clause(clause, env, &self.resources))
                                .collect::<Result<Vec<_>, _>>()?;
                            let condition = self.expr(condition, env)?;
                            expect_type(
                                condition.ty,
                                Type::Bool,
                                condition.span,
                                span,
                                "while condition requires bool",
                            )?;
                            let body = self.expr(body, env)?;
                            expect_type(
                                body.ty,
                                Type::Unit,
                                body.span,
                                span,
                                "while body requires unit; discard a result with a semicolon",
                            )?;
                            let depth = condition.depth.max(body.depth) + 1;
                            let value = self.node(
                                Type::Unit,
                                ExprKind::While {
                                    condition: Box::new(condition),
                                    body: Box::new(body),
                                },
                                span,
                                depth,
                            )?;
                            self.loops
                                .insert(value.id, LoopAnnotation { head, clauses });
                            self.push_binding(env, None, Type::Unit, false, span);
                            initializers.push((value, false));
                        }
                        syntax::Statement::Discard(value) => {
                            let value = self.expr(value, env)?;
                            self.push_binding(env, None, value.ty, false, value.span);
                            initializers.push((value, false));
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
                for (value, mutable) in initializers.into_iter().rev() {
                    let depth = value.depth.max(body.depth) + 1;
                    let ty = body.ty;
                    let kind = if mutable {
                        ExprKind::LetMut {
                            value: Box::new(value),
                            body: Box::new(body),
                        }
                    } else {
                        ExprKind::Let {
                            value: Box::new(value),
                            body: Box::new(body),
                        }
                    };
                    body = self.node(ty, kind, span, depth)?;
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
                let ty = op.result(operand.ty).ok_or_else(|| {
                    Diagnostic::new(span, "unary operator does not accept this operand type")
                })?;
                let depth = operand.depth + 1;
                (
                    ty,
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
                self.ordinary_name(&name, env, span)?;
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
                if signature.view.is_some() {
                    return Err(Diagnostic::new(span, "function requires a view argument"));
                }
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

#[cfg(test)]
mod annotation_tests {
    use super::*;

    fn locals(expr: &LocalAssertion, result: &mut Vec<usize>) {
        match &expr.kind {
            LocalAssertionKind::Tuple(fields) => {
                for field in fields {
                    locals(field, result);
                }
            }
            LocalAssertionKind::Project { value, .. } => locals(value, result),
            LocalAssertionKind::Local(index) => result.push(*index),
            LocalAssertionKind::Unary { operand, .. } => locals(operand, result),
            LocalAssertionKind::Binary { left, right, .. } => {
                locals(left, result);
                locals(right, result);
            }
            _ => {}
        }
    }

    fn head<'a>(
        contract: &'a FunctionContract,
        annotation: &LoopAnnotation,
    ) -> Vec<(Option<&'a str>, Type, bool)> {
        let mut result = Vec::new();
        let mut next = annotation.head;
        while let Some(id) = next {
            let binding = &contract.bindings[id.0];
            result.push((binding.name.as_deref(), binding.ty, binding.mutable));
            assert!(binding.parent.is_none_or(|parent| parent.0 < id.0));
            next = binding.parent;
        }
        result
    }

    #[test]
    fn loop_heads_count_discard_cells_and_restore_shadowed_parent_chains() {
        let source = "fn f(p:i64)->i64 {let mut x=p;9;x=x+1;
            while(false) invariant x>=p; {
                let before=x;7;while(false) invariant before==x; {}
            }
            {let x=true;while(false) invariant x; {}};
            while(false) invariant x>=p; {}
            x}";
        let program = crate::compile(source).unwrap();
        let contract = &program.contracts.as_ref().unwrap()[0];
        let mut loops: Vec<_> = contract.loops.values().collect();
        loops.sort_by_key(|annotation| annotation.clauses[0].span.start);
        let expected_indices = [vec![2, 3], vec![1, 4], vec![0], vec![4, 5]];
        for (annotation, expected) in loops.iter().zip(expected_indices) {
            let mut indices = Vec::new();
            locals(&annotation.clauses[0].expr, &mut indices);
            assert_eq!(indices, expected);
            assert!(
                source[annotation.clauses[0].span.start..annotation.clauses[0].span.end]
                    .starts_with("invariant ")
            );
        }
        use Type::{Bool, I64, Unit};
        let p = (Some("p"), I64, false);
        let x = (Some("x"), I64, true);
        let unit = (None, Unit, false);
        let integer = (None, I64, false);
        assert_eq!(head(contract, loops[0]), vec![unit, integer, x, p]);
        assert_eq!(
            head(contract, loops[1]),
            vec![integer, (Some("before"), I64, false), unit, integer, x, p]
        );
        assert_eq!(
            head(contract, loops[2]),
            vec![(Some("x"), Bool, false), unit, unit, integer, x, p]
        );
        assert_eq!(
            head(contract, loops[3]),
            vec![unit, unit, unit, integer, x, p]
        );
        let x_binding = &contract.bindings[1];
        assert_eq!(&source[x_binding.span.start..x_binding.span.end], "x");
    }

    fn while_ids(expr: &Expr, result: &mut Vec<usize>) {
        match &expr.kind {
            ExprKind::While { condition, body } => {
                result.push(expr.id);
                while_ids(condition, result);
                while_ids(body, result);
            }
            ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                while_ids(value, result);
                while_ids(body, result);
            }
            ExprKind::Assign { value, .. } => while_ids(value, result),
            ExprKind::Unary { operand, .. } => while_ids(operand, result),
            ExprKind::Binary { left, right, .. } => {
                while_ids(left, result);
                while_ids(right, result);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                while_ids(condition, result);
                while_ids(then_branch, result);
                while_ids(else_branch, result);
            }
            ExprKind::Call { arguments, .. } => {
                for argument in arguments {
                    while_ids(argument, result);
                }
            }
            _ => {}
        }
    }

    #[test]
    fn metadata_covers_nested_condition_body_and_argument_loops_without_changing_ids() {
        let source = "fn take(x:unit)->bool {false}
            fn main()->i64 {let mut x=0;
            while ({while(false) invariant x==0; {} false}) invariant x==0; {
                take({while(false) invariant x==0; {}});
                while(false) {}
            } 42}";
        let annotated = crate::compile(source).unwrap();
        let bare = crate::compile(&source.replace(" invariant x==0;", "")).unwrap();
        assert_eq!(annotated.functions.len(), bare.functions.len());
        for (index, function) in annotated.functions.iter().enumerate() {
            let mut ids = Vec::new();
            while_ids(&function.body, &mut ids);
            let mut bare_ids = Vec::new();
            while_ids(&bare.functions[index].body, &mut bare_ids);
            assert_eq!(ids, bare_ids);
            ids.sort();
            let contract = &annotated.contracts.as_ref().unwrap()[index];
            let plain_contract = &bare.contracts.as_ref().unwrap()[index];
            assert_eq!(ids, contract.loops.keys().copied().collect::<Vec<_>>());
            assert_eq!(contract.bindings.len(), plain_contract.bindings.len());
            for (a, b) in contract.bindings.iter().zip(&plain_contract.bindings) {
                assert_eq!(
                    (a.parent, &a.name, a.ty, a.mutable),
                    (b.parent, &b.name, b.ty, b.mutable)
                );
            }
            for (id, annotation) in &contract.loops {
                assert_eq!(annotation.head, plain_contract.loops[id].head);
            }
        }
        let contracts = annotated.contracts.as_ref().unwrap();
        assert!(contracts[0].bindings.is_empty());
        assert!(contracts[0].loops.is_empty());
        assert_eq!(contracts[1].loops.len(), 4);
        assert_eq!(
            contracts[1]
                .loops
                .values()
                .filter(|a| a.clauses.is_empty())
                .count(),
            1
        );
    }

    #[test]
    fn persistent_context_table_grows_once_per_binding_not_once_per_head() {
        let params = (0..80)
            .map(|i| format!("p{i}:i64"))
            .collect::<Vec<_>>()
            .join(",");
        let loops = "while(false) invariant p0==p79; {}".repeat(70);
        let program = crate::compile(&format!("fn many({params})->unit {{{loops}}}")).unwrap();
        let contract = &program.contracts.as_ref().unwrap()[0];
        assert_eq!(contract.bindings.len(), 150); // 80 params + 70 discarded loop results.
        assert_eq!(contract.loops.len(), 70);
        for (i, annotation) in contract.loops.values().enumerate() {
            assert_eq!(annotation.head, Some(BindingId(79 + i)));
            let mut indices = Vec::new();
            locals(&annotation.clauses[0].expr, &mut indices);
            assert_eq!(indices, vec![79 + i, i]);
        }
    }
}

#[cfg(test)]
mod product_metadata_tests {
    use super::*;
    #[test]
    fn scalar_specifications_keep_indices_across_tuple_parameters_and_locals() {
        let p=crate::compile("fn f(a:i64,p:(i64,),b:i64)->unit requires b>a; {let mut x=b;let q=(a,);while(false) invariant x>=a && b>=a;{}} ").unwrap();
        let contract = &p.contracts.as_ref().unwrap()[0];
        let SpecExprKind::Binary { left, right, .. } = &contract.requires[0].expr.kind else {
            panic!("binary clause")
        };
        assert!(matches!(left.kind, SpecExprKind::Param(2)));
        assert!(matches!(right.kind, SpecExprKind::Param(0)));
        fn locals(e: &LocalAssertion, ids: &mut Vec<usize>) {
            match &e.kind {
                LocalAssertionKind::Tuple(fields) => {
                    for field in fields {
                        locals(field, ids);
                    }
                }
                LocalAssertionKind::Project { value, .. } => locals(value, ids),
                LocalAssertionKind::Local(i) => ids.push(*i),
                LocalAssertionKind::Unary { operand, .. } => locals(operand, ids),
                LocalAssertionKind::Binary { left, right, .. } => {
                    locals(left, ids);
                    locals(right, ids)
                }
                _ => {}
            }
        }
        let annotation = contract.loops.values().next().unwrap();
        let mut ids = Vec::new();
        locals(&annotation.clauses[0].expr, &mut ids);
        assert_eq!(ids, vec![1, 4, 2, 4]);
        let mut head = annotation.head;
        let mut types = Vec::new();
        while let Some(id) = head {
            let binding = &contract.bindings[id.0];
            types.push(binding.ty);
            head = binding.parent;
        }
        assert!(matches!(types[0], Type::Tuple(_)));
        assert!(matches!(types[3], Type::Tuple(_)));
        assert_eq!(types.len(), 5);
    }
}
