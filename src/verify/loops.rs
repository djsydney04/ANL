//! Guarded obligations and normal-return flow for annotated invariant loops.
use super::{
    Failure, MAX_NODES, MAX_QUERIES, VerificationReport,
    formula::{Generator, Id, Pending, StateBudget, Symbolic, sort},
    location,
    solver::ModelSymbol,
};
use crate::{
    diagnostic::Span,
    types::{BinaryOp, Expr, ExprKind, LocalAssertion, LocalAssertionKind, Program, Type},
};
use serde_json::{Value, json};
use std::collections::BTreeMap;

pub(super) fn contains(program: &Program) -> bool {
    fn walk(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::While { .. } => true,
            ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                walk(value) || walk(body)
            }
            ExprKind::Assign { value, .. } => walk(value),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => walk(condition) || walk(then_branch) || walk(else_branch),
            ExprKind::Unary { operand, .. } => walk(operand),
            ExprKind::Binary { left, right, .. } => walk(left) || walk(right),
            ExprKind::Call { arguments, .. } => arguments.iter().any(walk),
            _ => false,
        }
    }
    program.functions.iter().any(|f| walk(&f.body))
}

fn invalid(message: &str) -> Failure {
    Failure::Error(message.into())
}

fn assertion_type(
    e: &LocalAssertion,
    env: &[(Type, bool)],
    budget: &mut StateBudget,
) -> Result<Type, Failure> {
    budget.charge(1)?;
    let ty = match &e.kind {
        LocalAssertionKind::Integer(_) => Type::I64,
        LocalAssertionKind::Boolean(_) => Type::Bool,
        LocalAssertionKind::Unit => Type::Unit,
        LocalAssertionKind::Local(i) => env
            .len()
            .checked_sub(i + 1)
            .and_then(|j| env.get(j))
            .map(|c| c.0)
            .ok_or_else(|| invalid("invalid invariant local index"))?,
        LocalAssertionKind::Unary { op, operand } => {
            if assertion_type(operand, env, budget)? != op.input() {
                return Err(invalid("invalid invariant operand type"));
            }
            op.input()
        }
        LocalAssertionKind::Binary { op, left, right } => op
            .result(
                assertion_type(left, env, budget)?,
                assertion_type(right, env, budget)?,
            )
            .ok_or_else(|| invalid("invalid invariant binary type"))?,
    };
    if e.ty.scalar_type() != ty {
        return Err(invalid("invalid invariant result type"));
    }
    Ok(ty)
}

pub(super) fn preflight(
    program: &Program,
    report: &mut VerificationReport,
    budget: &mut StateBudget,
) -> Result<(), Failure> {
    let contracts = program
        .contracts
        .as_ref()
        .ok_or_else(|| Failure::Unsupported("source contracts are absent".into()))?;
    if contracts.len() != program.functions.len() {
        return Err(invalid("source contract table length mismatch"));
    }
    let mut edges = Vec::new();
    budget.reserve(&mut edges, program.functions.len())?;
    edges.resize_with(program.functions.len(), Vec::new);
    let mut count = 0;
    struct Walk<'a> {
        program: &'a Program,
        function: usize,
        count: &'a mut usize,
        budget: &'a mut StateBudget,
        edges: &'a mut Vec<usize>,
        loops: &'a mut Vec<Value>,
    }
    impl Walk<'_> {
        fn expr(&mut self, e: &Expr, env: &mut Vec<(Type, bool)>) -> Result<(), Failure> {
            self.budget.charge(1)?;
            *self.count += 1;
            if *self.count > MAX_NODES {
                return Err(Failure::Unknown(
                    "program expression count exceeds 100000".into(),
                ));
            }
            match &e.kind {
                ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                    self.expr(value, env)?;
                    self.budget.reserve(env, 1)?;
                    env.push((value.ty, matches!(e.kind, ExprKind::LetMut { .. })));
                    self.expr(body, env)?;
                    env.pop();
                }
                ExprKind::Assign { value, .. } => self.expr(value, env)?,
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    self.expr(condition, env)?;
                    self.expr(then_branch, env)?;
                    self.expr(else_branch, env)?;
                }
                ExprKind::Unary { operand, .. } => self.expr(operand, env)?,
                ExprKind::Binary { left, right, .. } => {
                    self.expr(left, env)?;
                    self.expr(right, env)?;
                }
                ExprKind::Call {
                    function,
                    arguments,
                } => {
                    if *function >= self.program.functions.len() {
                        return Err(invalid("invalid checked callee"));
                    }
                    self.budget.reserve(self.edges, 1)?;
                    self.edges.push(*function);
                    for arg in arguments {
                        self.expr(arg, env)?;
                    }
                }
                ExprKind::While { condition, body } => {
                    let contract =
                        &self.program.contracts.as_ref().expect("contracts")[self.function];
                    let annotation = contract.loops.get(&e.id).ok_or_else(|| {
                        Failure::Unsupported("loop annotation metadata is absent".into())
                    })?;
                    if annotation.clauses.is_empty() {
                        return Err(Failure::Unsupported(format!(
                            "while in function {} requires at least one invariant clause",
                            contract.source_name
                        )));
                    }
                    let mut parent = annotation.head;
                    for &(ty, mutable) in env.iter().rev() {
                        self.budget.charge(1)?;
                        let id = parent.ok_or_else(|| {
                            invalid("loop head context is shorter than checked scope")
                        })?;
                        let binding = contract
                            .bindings
                            .get(id.0)
                            .ok_or_else(|| invalid("invalid source binding ID"))?;
                        if binding.ty != ty || binding.mutable != mutable {
                            return Err(invalid("loop head context permission/type mismatch"));
                        }
                        parent = binding.parent;
                    }
                    if parent.is_some() {
                        return Err(invalid("loop head context is longer than checked scope"));
                    }
                    let mut clauses = Vec::new();
                    self.budget
                        .reserve(&mut clauses, annotation.clauses.len())?;
                    for (index, clause) in annotation.clauses.iter().enumerate() {
                        if assertion_type(&clause.expr, env, self.budget)? != Type::Bool {
                            return Err(invalid("invariant is not Boolean"));
                        }
                        self.budget.charge(2)?;
                        clauses.push(
                            json!({"index":index,"location":location(self.program,clause.span)}),
                        );
                    }
                    self.budget.reserve(self.loops, 1)?;
                    let mut record = json!({"node_id":e.id,"location":location(self.program,e.span),"head_binding":annotation.head.map(|id|id.0)});
                    record["clauses"] = Value::Array(clauses);
                    self.loops.push(record);
                    self.expr(condition, env)?;
                    self.expr(body, env)?;
                }
                _ => {}
            }
            Ok(())
        }
    }
    for (id, function) in program.functions.iter().enumerate() {
        let contract = &contracts[id];
        let mut bindings = Vec::new();
        budget.reserve(&mut bindings, contract.bindings.len())?;
        for (index, binding) in contract.bindings.iter().enumerate() {
            budget.charge(6)?;
            if binding.parent.is_some_and(|p| p.0 >= index) {
                return Err(invalid("invalid source binding parent"));
            }
            bindings.push(json!({"id":index,"parent":binding.parent.map(|p|p.0),"name":binding.name,"type":binding.ty.as_str(),"mutable":binding.mutable,"location":location(program,binding.span)}));
        }
        let mut env = Vec::new();
        budget.reserve(&mut env, function.params.len())?;
        env.extend(function.params.iter().map(|t| (*t, false)));
        let mut loops = Vec::new();
        Walk {
            program,
            function: id,
            count: &mut count,
            budget,
            edges: &mut edges[id],
            loops: &mut loops,
        }
        .expr(&function.body, &mut env)?;
        if loops.len() != contract.loops.len() {
            return Err(invalid("loop metadata contains an unmatched node"));
        }
        budget.charge(loops.len().saturating_mul(20))?;
        loops.sort_by_key(|v| v["node_id"].as_u64());
        let clauses = loops
            .iter()
            .map(|v| v["clauses"].as_array().expect("clauses").len())
            .sum::<usize>();
        report.data["functions"][id]["invariant_clauses"] = json!(clauses);
        report.data["functions"][id]["bindings"] = Value::Array(bindings);
        report.data["functions"][id]["loops"] = Value::Array(loops);
    }
    report.data["source_loop_metadata_complete"] = json!(true);
    budget.charge(program.functions.len())?;
    let mut indegree = vec![0usize; program.functions.len()];
    for list in &edges {
        for &callee in list {
            budget.charge(1)?;
            indegree[callee] += 1;
        }
    }
    let mut ready = Vec::new();
    budget.reserve(&mut ready, indegree.len())?;
    for (id, degree) in indegree.iter().enumerate() {
        budget.charge(1)?;
        if *degree == 0 {
            ready.push(id);
        }
    }
    let mut visited = 0;
    while let Some(id) = ready.pop() {
        visited += 1;
        for &callee in &edges[id] {
            budget.charge(1)?;
            indegree[callee] -= 1;
            if indegree[callee] == 0 {
                ready.push(callee);
            }
        }
    }
    if visited != program.functions.len() {
        return Err(Failure::Unsupported(
            "recursive function calls are outside apl-loop-verify-v1".into(),
        ));
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct Frame {
    function: usize,
    expansion: usize,
}
#[derive(Clone, Copy)]
struct LoopSite {
    frame: Frame,
    node: usize,
    occurrence: usize,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum CellKey {
    Parameter(usize),
    Let(usize),
}
#[derive(Clone, Copy)]
struct Cell {
    value: Id,
    ty: Type,
    mutable: bool,
    key: CellKey,
}
struct Flow {
    value: Id,
    env: Vec<Cell>,
    normal: Id,
}
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    Pre(usize),
    Reachable,
    Body,
    Invariant(usize, bool, usize),
    Post(usize),
}
struct Check {
    guard: Id,
    required: Id,
    implication: Id,
    span: Span,
    function: usize,
    expansion: usize,
    origin: Value,
}
pub(super) struct LoopPending {
    pub pending: Pending,
    pub checks: Value,
}
pub(super) struct Artifact {
    pub pending: Vec<LoopPending>,
    pub heads: Vec<ModelSymbol>,
}
struct Analysis<'g, 'p, 'r> {
    genr: &'g mut Generator<'p>,
    report: &'r mut VerificationReport,
    root: usize,
    checks: Vec<Check>,
    groups: BTreeMap<Key, Vec<usize>>,
    heads: Vec<ModelSymbol>,
}
impl Analysis<'_, '_, '_> {
    fn group(&mut self, key: Key) -> Result<(), Failure> {
        if !self.groups.contains_key(&key) {
            let budget = self.genr.arena.budget()?;
            if budget.pending_queries >= MAX_QUERIES {
                return Err(Failure::Unknown("verification exceeds 1024 queries".into()));
            }
            budget.charge(1)?;
            budget.pending_queries += 1;
            self.groups.insert(key, Vec::new());
        }
        Ok(())
    }
    fn check(
        &mut self,
        key: Key,
        guard: Id,
        required: Id,
        span: Span,
        frame: Frame,
        origin: Value,
    ) -> Result<(), Failure> {
        let Frame {
            function,
            expansion,
        } = frame;
        self.group(key)?;
        let implication = self.genr.arena.implies(guard, required)?;
        let id = self.checks.len();
        self.genr.arena.reserve(&mut self.checks, 1)?;
        self.checks.push(Check {
            guard,
            required,
            implication,
            span,
            function,
            expansion,
            origin,
        });
        let ids = self.groups.get_mut(&key).expect("registered group");
        self.genr.arena.reserve(ids, 1)?;
        ids.push(id);
        Ok(())
    }
    fn expansion(
        &mut self,
        function: usize,
        parent: Option<usize>,
        call: Option<&Expr>,
    ) -> Result<usize, Failure> {
        let budget = self.genr.arena.budget()?;
        budget.charge(6)?;
        let id = budget.expansions;
        budget.expansions += 1;
        let values = self.report.data["expansions"]
            .as_array_mut()
            .expect("expansions");
        budget.reserve(values, 1)?;
        values.push(json!({"id":id,"verification_function_id":self.root,"source_function_id":function,"parent_expansion_id":parent,"call_node_id":call.map(|e|e.id),"location":location(self.genr.program,call.map_or(self.genr.program.functions[function].span,|e|e.span))}));
        Ok(id)
    }
    fn copy(&mut self, env: &[Cell]) -> Result<Vec<Cell>, Failure> {
        let mut result = Vec::new();
        self.genr.arena.reserve(&mut result, env.len())?;
        for cell in env {
            self.genr.arena.work(1)?;
            result.push(*cell);
        }
        Ok(result)
    }
    fn entry(&mut self, values: &[Id], types: &[Type]) -> Result<Vec<Cell>, Failure> {
        if values.len() != types.len() {
            return Err(invalid("symbolic call arity mismatch"));
        }
        let mut env = Vec::new();
        self.genr.arena.reserve(&mut env, values.len())?;
        for (index, (&value, &ty)) in values.iter().zip(types).enumerate() {
            self.genr.arena.work(1)?;
            env.push(Cell {
                value,
                ty,
                mutable: false,
                key: CellKey::Parameter(index),
            });
        }
        Ok(env)
    }
    fn ite(&mut self, ty: Type, condition: Id, yes: Id, no: Id) -> Result<Id, Failure> {
        if ty == Type::Unit {
            return self.genr.arena.int("0");
        }
        if yes == no {
            return Ok(yes);
        }
        self.genr.arena.app(
            sort(ty),
            format!("(ite n{condition} n{yes} n{no})"),
            &[condition, yes, no],
        )
    }
    fn merge(&mut self, condition: Id, yes: Flow, mut no: Flow, ty: Type) -> Result<Flow, Failure> {
        if yes.env.len() != no.env.len() {
            return Err(invalid("symbolic branch scope mismatch"));
        }
        for (a, b) in yes.env.iter().zip(&mut no.env) {
            self.genr.arena.work(1)?;
            if a.ty != b.ty || a.mutable != b.mutable || a.key != b.key {
                return Err(invalid("symbolic branch binding mismatch"));
            }
            b.value = self.ite(a.ty, condition, a.value, b.value)?;
        }
        let value = self.ite(ty, condition, yes.value, no.value)?;
        let normal = self.genr.arena.app(
            "Bool",
            format!("(or n{} n{})", yes.normal, no.normal),
            &[yes.normal, no.normal],
        )?;
        Ok(Flow {
            value,
            env: no.env,
            normal,
        })
    }
    fn assertion(
        &mut self,
        expr: &LocalAssertion,
        env: &[Cell],
        depth: usize,
    ) -> Result<Symbolic, Failure> {
        self.genr.visit(depth)?;
        let safe = self.genr.arena.truth()?;
        let value = match &expr.kind {
            LocalAssertionKind::Integer(n) => self.genr.arena.int(n)?,
            LocalAssertionKind::Boolean(b) => self.genr.arena.bool(*b)?,
            LocalAssertionKind::Unit => self.genr.arena.int("0")?,
            LocalAssertionKind::Local(i) => {
                self.genr.arena.work(1)?;
                env.len()
                    .checked_sub(i + 1)
                    .and_then(|j| env.get(j))
                    .ok_or_else(|| invalid("invalid invariant local"))?
                    .value
            }
            LocalAssertionKind::Unary { op, operand } => {
                let a = self.assertion(operand, env, depth + 1)?;
                return self.genr.unary(*op, a, false);
            }
            LocalAssertionKind::Binary { op, left, right } => {
                let a = self.assertion(left, env, depth + 1)?;
                let b = self.assertion(right, env, depth + 1)?;
                return self.genr.binary(*op, a, b, expr.ty.scalar_type(), false);
            }
        };
        Ok(Symbolic { value, safe })
    }
    fn invariant(
        &mut self,
        site: LoopSite,
        preserve: Option<bool>,
        env: &[Cell],
        normal: Id,
        depth: usize,
    ) -> Result<Id, Failure> {
        let LoopSite {
            frame: Frame {
                function,
                expansion,
            },
            node,
            occurrence,
        } = site;
        let clauses = &self.genr.program.contracts.as_ref().expect("contracts")[function].loops
            [&node]
            .clauses;
        let mut truths = Vec::new();
        self.genr.arena.reserve(&mut truths, clauses.len())?;
        for (index, clause) in clauses.iter().enumerate() {
            let a = self.assertion(&clause.expr, env, depth + 1)?;
            let required = self.genr.arena.and(&[a.safe, a.value])?;
            if let Some(preserved) = preserve {
                self.genr.arena.work(4)?;
                self.check(Key::Invariant(occurrence,preserved,index),normal,required,clause.span,Frame{function,expansion},
                    json!({"kind":if preserved{"loop_invariant_preserved"}else{"loop_invariant_initialized"},"loop_node_id":node,"occurrence_id":occurrence,"clause_index":index}))?;
            }
            truths.push(required);
        }
        self.genr.arena.and(&truths)
    }
    fn expr(
        &mut self,
        expr: &Expr,
        function: usize,
        expansion: usize,
        mut env: Vec<Cell>,
        normal: Id,
        depth: usize,
    ) -> Result<Flow, Failure> {
        self.genr.visit(depth)?;
        let value = match &expr.kind {
            ExprKind::Tuple(_) | ExprKind::Project { .. } => {
                return Err(Failure::Unsupported(
                    "flat products are outside scalar verification".into(),
                ));
            }
            ExprKind::Integer(n) => self.genr.arena.int(&if *n < 0 {
                format!("(- {})", n.unsigned_abs())
            } else {
                n.to_string()
            })?,
            ExprKind::Boolean(b) => self.genr.arena.bool(*b)?,
            ExprKind::Unit => self.genr.arena.int("0")?,
            ExprKind::Local(i) => {
                self.genr.arena.work(1)?;
                env.len()
                    .checked_sub(i + 1)
                    .and_then(|j| env.get(j))
                    .ok_or_else(|| invalid("invalid checked local"))?
                    .value
            }
            ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                let mut initial = self.expr(value, function, expansion, env, normal, depth + 1)?;
                self.genr.arena.reserve(&mut initial.env, 1)?;
                initial.env.push(Cell {
                    value: initial.value,
                    ty: value.ty,
                    mutable: matches!(expr.kind, ExprKind::LetMut { .. }),
                    key: CellKey::Let(expr.id),
                });
                let mut result = self.expr(
                    body,
                    function,
                    expansion,
                    initial.env,
                    initial.normal,
                    depth + 1,
                )?;
                self.genr.arena.work(1)?;
                if result
                    .env
                    .pop()
                    .is_none_or(|cell| cell.key != CellKey::Let(expr.id))
                {
                    return Err(invalid("symbolic let scope mismatch"));
                }
                return Ok(result);
            }
            ExprKind::Assign { index, value } => {
                let mut result = self.expr(value, function, expansion, env, normal, depth + 1)?;
                self.genr.arena.work(1)?;
                let target = result
                    .env
                    .len()
                    .checked_sub(index + 1)
                    .and_then(|i| result.env.get_mut(i))
                    .ok_or_else(|| invalid("invalid checked assignment"))?;
                if !target.mutable || target.ty != value.ty {
                    return Err(invalid("invalid assignment permission/type"));
                }
                target.value = result.value;
                result.value = self.genr.arena.int("0")?;
                return Ok(result);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let c = self.expr(condition, function, expansion, env, normal, depth + 1)?;
                let yes_env = self.copy(&c.env)?;
                let yes_path = self.genr.arena.and(&[c.normal, c.value])?;
                let no_condition = self.genr.arena.not(c.value)?;
                let no_path = self.genr.arena.and(&[c.normal, no_condition])?;
                let yes = self.expr(
                    then_branch,
                    function,
                    expansion,
                    yes_env,
                    yes_path,
                    depth + 1,
                )?;
                let no = self.expr(else_branch, function, expansion, c.env, no_path, depth + 1)?;
                return self.merge(c.value, yes, no, expr.ty);
            }
            ExprKind::Unary { op, operand } => {
                let a = self.expr(operand, function, expansion, env, normal, depth + 1)?;
                let safe = self.genr.arena.truth()?;
                let result = self.genr.unary(
                    *op,
                    Symbolic {
                        value: a.value,
                        safe,
                    },
                    true,
                )?;
                self.genr.arena.work(3)?;
                self.check(
                    Key::Body,
                    a.normal,
                    result.safe,
                    expr.span,
                    Frame {
                        function,
                        expansion,
                    },
                    json!({"kind":"arithmetic","node_id":expr.id,"operator":op.as_str()}),
                )?;
                return Ok(Flow {
                    value: result.value,
                    ..a
                });
            }
            ExprKind::Binary { op, left, right } => {
                let a = self.expr(left, function, expansion, env, normal, depth + 1)?;
                if matches!(op, BinaryOp::And | BinaryOp::Or) {
                    let skip_env = self.copy(&a.env)?;
                    let not_left = self.genr.arena.not(a.value)?;
                    let (execute, skip) = if *op == BinaryOp::And {
                        (a.value, not_left)
                    } else {
                        (not_left, a.value)
                    };
                    let path = self.genr.arena.and(&[a.normal, execute])?;
                    let skip_path = self.genr.arena.and(&[a.normal, skip])?;
                    let b = self.expr(right, function, expansion, a.env, path, depth + 1)?;
                    let skipped = Flow {
                        value: a.value,
                        env: skip_env,
                        normal: skip_path,
                    };
                    return if *op == BinaryOp::And {
                        self.merge(a.value, b, skipped, Type::Bool)
                    } else {
                        self.merge(a.value, skipped, b, Type::Bool)
                    };
                }
                let b = self.expr(right, function, expansion, a.env, a.normal, depth + 1)?;
                let safe = self.genr.arena.truth()?;
                let result = self.genr.binary(
                    *op,
                    Symbolic {
                        value: a.value,
                        safe,
                    },
                    Symbolic {
                        value: b.value,
                        safe,
                    },
                    expr.ty,
                    true,
                )?;
                self.genr.arena.work(3)?;
                self.check(
                    Key::Body,
                    b.normal,
                    result.safe,
                    expr.span,
                    Frame {
                        function,
                        expansion,
                    },
                    json!({"kind":"arithmetic","node_id":expr.id,"operator":op.as_str()}),
                )?;
                return Ok(Flow {
                    value: result.value,
                    ..b
                });
            }
            ExprKind::Call {
                function: callee,
                arguments,
            } => {
                let mut values = Vec::new();
                self.genr.arena.reserve(&mut values, arguments.len())?;
                let mut path = normal;
                for argument in arguments {
                    let a = self.expr(argument, function, expansion, env, path, depth + 1)?;
                    values.push(a.value);
                    env = a.env;
                    path = a.normal;
                }
                let contract = &self.genr.program.contracts.as_ref().expect("contracts")[*callee];
                let mut defined = Vec::new();
                let mut clauses = Vec::new();
                self.genr
                    .arena
                    .reserve(&mut defined, contract.requires.len())?;
                self.genr
                    .arena
                    .reserve(&mut clauses, contract.requires.len())?;
                let mut truth = self.genr.arena.truth()?;
                for (index, clause) in contract.requires.iter().enumerate() {
                    let pre = self.genr.spec(&clause.expr, &values, None, depth + 1)?;
                    defined.push(self.genr.arena.implies(truth, pre.safe)?);
                    truth = self.genr.arena.and(&[truth, pre.value])?;
                    self.genr.arena.work(4)?;
                    clauses.push(json!({"index":index,"location":location(self.genr.program,clause.span),"defined":format!("n{}",pre.safe),"truth":format!("n{}",pre.value)}));
                }
                let defined = self.genr.arena.and(&defined)?;
                let required = self.genr.arena.and(&[defined, truth])?;
                self.genr.arena.work(4)?;
                let mut origin = json!({"kind":"call_preconditions","call_node_id":expr.id,"callee_function_id":callee});
                origin["clauses"] = Value::Array(clauses);
                self.check(
                    Key::Body,
                    path,
                    required,
                    expr.span,
                    Frame {
                        function,
                        expansion,
                    },
                    origin,
                )?;
                let callee_fn = &self.genr.program.functions[*callee];
                let callee_env = self.entry(&values, &callee_fn.params)?;
                let child = self.expansion(*callee, Some(expansion), Some(expr))?;
                let result =
                    self.expr(&callee_fn.body, *callee, child, callee_env, path, depth + 1)?;
                return Ok(Flow {
                    value: result.value,
                    env,
                    normal: result.normal,
                });
            }
            ExprKind::While { condition, body } => {
                let budget = self.genr.arena.budget()?;
                budget.charge(1)?;
                let occurrence = budget.occurrences;
                budget.occurrences += 1;
                let record_index = self.report.data["loop_occurrences"]
                    .as_array()
                    .expect("occurrences")
                    .len();
                let records = self.report.data["loop_occurrences"]
                    .as_array_mut()
                    .expect("occurrences");
                budget.reserve(records, 1)?;
                budget.charge(6)?;
                records.push(json!({"id":occurrence,"expansion_id":expansion,"source_function_id":function,"loop_node_id":expr.id,"location":location(self.genr.program,expr.span),"head_symbols":[]}));
                self.invariant(
                    LoopSite {
                        frame: Frame {
                            function,
                            expansion,
                        },
                        node: expr.id,
                        occurrence,
                    },
                    Some(false),
                    &env,
                    normal,
                    depth,
                )?;
                let contract = &self.genr.program.contracts.as_ref().expect("contracts")[function];
                let mut parent = contract.loops[&expr.id].head;
                let mut domain = Vec::new();
                self.genr.arena.reserve(&mut domain, env.len())?;
                for cell in env.iter_mut().rev() {
                    self.genr.arena.work(1)?;
                    let binding = parent.ok_or_else(|| invalid("missing loop head binding"))?;
                    let source = &contract.bindings[binding.0];
                    parent = source.parent;
                    if cell.ty != source.ty || cell.mutable != source.mutable {
                        return Err(invalid("loop head binding mismatch"));
                    }
                    if cell.mutable && cell.ty != Type::Unit {
                        let (id, value) = self.genr.arena.head(cell.ty)?;
                        cell.value = value;
                        self.genr.arena.work(8)?;
                        let origin = json!({"kind":"loop_head","source_function_id":function,"loop_node_id":expr.id,"expansion_id":expansion,"occurrence_id":occurrence,"binding_id":binding.0});
                        self.genr.arena.reserve(&mut self.heads, 1)?;
                        self.heads.push(ModelSymbol {
                            name: format!("h{id}"),
                            ty: cell.ty,
                            origin,
                            head: Some(id),
                        });
                        let symbols =
                            self.report.data["loop_occurrences"][record_index]["head_symbols"]
                                .as_array_mut()
                                .expect("head symbols");
                        self.genr.arena.reserve(symbols, 1)?;
                        symbols.push(json!({"symbol":format!("h{id}"),"type":cell.ty.as_str(),"binding_id":binding.0}));
                        if cell.ty == Type::I64 {
                            domain.push(self.genr.arena.range(value)?);
                        }
                    }
                }
                if parent.is_some() {
                    return Err(invalid("extra loop head binding"));
                }
                let head_domain = self.genr.arena.and(&domain)?;
                let invariant = self.invariant(
                    LoopSite {
                        frame: Frame {
                            function,
                            expansion,
                        },
                        node: expr.id,
                        occurrence,
                    },
                    None,
                    &env,
                    normal,
                    depth,
                )?;
                let head_path = self.genr.arena.and(&[normal, head_domain, invariant])?;
                let condition =
                    self.expr(condition, function, expansion, env, head_path, depth + 1)?;
                let body_env = self.copy(&condition.env)?;
                let body_path = self.genr.arena.and(&[condition.normal, condition.value])?;
                let body = self.expr(body, function, expansion, body_env, body_path, depth + 1)?;
                self.invariant(
                    LoopSite {
                        frame: Frame {
                            function,
                            expansion,
                        },
                        node: expr.id,
                        occurrence,
                    },
                    Some(true),
                    &body.env,
                    body.normal,
                    depth,
                )?;
                let false_value = self.genr.arena.not(condition.value)?;
                let normal = self.genr.arena.and(&[condition.normal, false_value])?;
                return Ok(Flow {
                    value: self.genr.arena.int("0")?,
                    env: condition.env,
                    normal,
                });
            }
        };
        Ok(Flow { value, env, normal })
    }
}

pub(super) fn obligations(
    genr: &mut Generator<'_>,
    function: usize,
    report: &mut VerificationReport,
) -> Result<Artifact, Failure> {
    genr.arena.tracking();
    let f = &genr.program.functions[function];
    let contract = &genr.program.contracts.as_ref().expect("contracts")[function];
    let mut analysis = Analysis {
        genr,
        report,
        root: function,
        checks: Vec::new(),
        groups: BTreeMap::new(),
        heads: Vec::new(),
    };
    let expansion = analysis.expansion(function, None, None)?;
    let (params, mut assumptions) = analysis.genr.parameters(&f.params)?;
    for (index, clause) in contract.requires.iter().enumerate() {
        let pre = analysis.genr.spec(&clause.expr, &params, None, 0)?;
        analysis.genr.arena.work(2)?;
        analysis.check(
            Key::Pre(index),
            assumptions,
            pre.safe,
            clause.span,
            Frame {
                function,
                expansion,
            },
            json!({"kind":"entry_precondition","clause_index":index}),
        )?;
        assumptions = analysis
            .genr
            .arena
            .and(&[assumptions, pre.safe, pre.value])?;
    }
    analysis.group(Key::Reachable)?;
    analysis.group(Key::Body)?;
    let env = analysis.entry(&params, &f.params)?;
    let body = analysis.expr(&f.body, function, expansion, env, assumptions, 0)?;
    for (index, clause) in contract.ensures.iter().enumerate() {
        let post = analysis
            .genr
            .spec(&clause.expr, &params, Some(body.value), 0)?;
        let required = analysis.genr.arena.and(&[post.safe, post.value])?;
        analysis.genr.arena.work(2)?;
        analysis.check(
            Key::Post(index),
            body.normal,
            required,
            clause.span,
            Frame {
                function,
                expansion,
            },
            json!({"kind":"postcondition","clause_index":index}),
        )?;
    }
    let mut pending = Vec::new();
    analysis
        .genr
        .arena
        .reserve(&mut pending, analysis.groups.len())?;
    let mut covered = 0;
    for (key, ids) in analysis.groups {
        analysis.genr.arena.work(ids.len())?;
        covered += ids.len();
        let mut implications = Vec::new();
        let mut checks = Vec::new();
        analysis.genr.arena.reserve(&mut implications, ids.len())?;
        analysis.genr.arena.reserve(&mut checks, ids.len())?;
        for id in ids {
            let check = &mut analysis.checks[id];
            analysis.genr.arena.work(9)?;
            implications.push(check.implication);
            let mut record = json!({"id":id,"source_function_id":check.function,"expansion_id":check.expansion,"location":location(analysis.genr.program,check.span),"guard":format!("n{}",check.guard),"required":format!("n{}",check.required),"implication":format!("n{}",check.implication)});
            record["origin"] = std::mem::take(&mut check.origin);
            checks.push(record);
        }
        let assertion = if key == Key::Reachable {
            assumptions
        } else {
            let conjunction = analysis.genr.arena.and(&implications)?;
            analysis.genr.arena.not(conjunction)?
        };
        let (kind, span) = match key {
            Key::Pre(index) => ("precondition_defined", contract.requires[index].span),
            Key::Reachable => ("precondition_satisfiable", f.span),
            Key::Body => ("body_safe", f.body.span),
            Key::Invariant(_, preserve, _) => {
                let span = checks
                    .first()
                    .and_then(|v| v["id"].as_u64())
                    .map(|id| analysis.checks[id as usize].span)
                    .ok_or_else(|| invalid("empty invariant group"))?;
                (
                    if preserve {
                        "loop_invariant_preserved"
                    } else {
                        "loop_invariant_initialized"
                    },
                    span,
                )
            }
            Key::Post(index) => ("postcondition", contract.ensures[index].span),
        };
        pending.push(LoopPending {
            pending: Pending {
                kind,
                span,
                assertion,
                expected_sat: key == Key::Reachable,
            },
            checks: Value::Array(checks),
        });
    }
    if covered != analysis.checks.len() {
        return Err(invalid("incomplete guarded check partition"));
    }
    Ok(Artifact {
        pending,
        heads: analysis.heads,
    })
}

pub(super) fn manifest(
    genr: &mut Generator<'_>,
    params: &[Type],
    heads: &[ModelSymbol],
    assertion: Id,
) -> Result<Vec<ModelSymbol>, Failure> {
    let relevant = genr.arena.relevant_heads(assertion)?;
    let mut symbols = Vec::new();
    genr.arena
        .reserve(&mut symbols, params.len() + relevant.len())?;
    for (index, &ty) in params.iter().enumerate() {
        genr.arena.work(1)?;
        if ty != Type::Unit {
            symbols.push(ModelSymbol {
                name: format!("p{index}"),
                ty,
                origin: json!({"kind":"parameter","index":index}),
                head: None,
            });
        }
    }
    let mut selected = relevant.into_iter().peekable();
    for head in heads {
        genr.arena.work(1)?;
        let id = head
            .head
            .ok_or_else(|| invalid("missing generated head identity"))?;
        if selected.peek() == Some(&id) {
            genr.arena.work(8)?;
            symbols.push(ModelSymbol {
                name: head.name.clone(),
                ty: head.ty,
                origin: head.origin.clone(),
                head: head.head,
            });
            selected.next();
        }
    }
    if selected.next().is_some() {
        return Err(invalid("missing relevant loop head"));
    }
    Ok(symbols)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{Duration, Instant};
    #[test]
    fn pending_query_budget_is_shared_before_group_allocation() {
        let program = crate::compile("fn f()->unit{while(false) invariant true;{}}").unwrap();
        let mut budget = StateBudget::new(Instant::now() + Duration::from_secs(5));
        budget.pending_queries = MAX_QUERIES - 1;
        let mut expanded = 0;
        let mut generator = Generator::with_state_budget(&program, &mut expanded, &mut budget);
        let mut report = VerificationReport {
            data: json!({"expansions":[],"loop_occurrences":[]}),
            exit: 0,
        };
        assert!(
            matches!(obligations(&mut generator,0,&mut report),Err(Failure::Unknown(message)) if message.contains("1024 queries"))
        );
        assert_eq!(
            generator.arena.budget().unwrap().pending_queries,
            MAX_QUERIES
        );
        assert!(
            report.data["loop_occurrences"]
                .as_array()
                .unwrap()
                .is_empty()
        );
    }
}
