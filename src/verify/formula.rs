use super::{Failure, MAX_NODES, MAX_QUERY_BYTES};
use crate::{
    diagnostic::Span,
    types::{BinaryOp, Expr, ExprKind, Program, SpecExpr, SpecExprKind, SpecType, Type, UnaryOp},
};

pub(super) type Id = usize;
#[derive(Clone, Copy)]
pub(super) struct Symbolic {
    pub value: Id,
    pub safe: Id,
}
struct Node {
    sort: &'static str,
    body: String,
}
pub(super) struct Arena {
    nodes: Vec<Node>,
    bytes: usize,
}
impl Arena {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            bytes: 0,
        }
    }
    pub fn add(&mut self, sort: &'static str, body: String) -> Result<Id, Failure> {
        self.bytes += format!("(define-fun n{} () {sort} {body})\n", self.nodes.len()).len();
        if self.bytes > MAX_QUERY_BYTES {
            return Err(Failure::Unknown(
                "generated query exceeds 1048576 bytes".into(),
            ));
        }
        let id = self.nodes.len();
        self.nodes.push(Node { sort, body });
        Ok(id)
    }
    pub fn truth(&mut self) -> Result<Id, Failure> {
        self.add("Bool", "true".into())
    }
    pub fn bool(&mut self, value: bool) -> Result<Id, Failure> {
        self.add("Bool", value.to_string())
    }
    pub fn int(&mut self, value: &str) -> Result<Id, Failure> {
        self.add("Int", value.into())
    }
    pub fn and(&mut self, ids: &[Id]) -> Result<Id, Failure> {
        if ids.is_empty() {
            return self.truth();
        }
        if ids.len() == 1 {
            return Ok(ids[0]);
        }
        self.add(
            "Bool",
            format!(
                "(and {})",
                ids.iter()
                    .map(|id| format!("n{id}"))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        )
    }
    pub fn not(&mut self, id: Id) -> Result<Id, Failure> {
        self.add("Bool", format!("(not n{id})"))
    }
    pub fn implies(&mut self, a: Id, b: Id) -> Result<Id, Failure> {
        self.add("Bool", format!("(=> n{a} n{b})"))
    }
    pub fn range(&mut self, id: Id) -> Result<Id, Failure> {
        self.add(
            "Bool",
            format!("(and (<= (- 9223372036854775808) n{id}) (<= n{id} 9223372036854775807))"),
        )
    }
    pub fn render(
        &self,
        params: &[Type],
        assertion: Id,
        timeout_ms: u128,
    ) -> Result<String, Failure> {
        let mut text = format!(
            "(set-option :print-success false)\n(set-option :produce-models true)\n(set-option :timeout {})\n",
            timeout_ms.max(1)
        );
        text.push_str("(define-fun apl_abs ((x Int)) Int (ite (< x 0) (- x) x))\n(define-fun apl_div ((a Int) (b Int)) Int (ite (= b 0) 0 (ite (= (< a 0) (< b 0)) (div (apl_abs a) (apl_abs b)) (- (div (apl_abs a) (apl_abs b))))))\n");
        for (i, ty) in params.iter().enumerate() {
            if *ty != Type::Unit {
                text.push_str(&format!("(declare-const p{i} {})\n", sort(*ty)));
            }
        }
        for (i, node) in self.nodes.iter().enumerate() {
            text.push_str(&format!(
                "(define-fun n{i} () {} {})\n",
                node.sort, node.body
            ));
        }
        text.push_str(&format!("(assert n{assertion})\n(check-sat)\n"));
        if text.len() > MAX_QUERY_BYTES {
            return Err(Failure::Unknown(
                "generated query exceeds 1048576 bytes".into(),
            ));
        }
        Ok(text)
    }
}
fn sort(ty: Type) -> &'static str {
    if ty == Type::Bool { "Bool" } else { "Int" }
}
fn spec_type(ty: SpecType) -> Type {
    match ty {
        SpecType::Int => Type::I64,
        SpecType::Bool => Type::Bool,
        SpecType::Unit => Type::Unit,
    }
}

pub(super) struct Generator<'a> {
    pub arena: Arena,
    program: &'a Program,
    pub expanded: &'a mut usize,
}
impl<'a> Generator<'a> {
    pub fn new(program: &'a Program, expanded: &'a mut usize) -> Self {
        Self {
            arena: Arena::new(),
            program,
            expanded,
        }
    }
    fn visit(&mut self, depth: usize) -> Result<(), Failure> {
        *self.expanded += 1;
        if *self.expanded > MAX_NODES {
            return Err(Failure::Unknown(
                "expanded expressions exceed 100000 nodes".into(),
            ));
        }
        if depth > 256 {
            return Err(Failure::Unknown(
                "verification expansion depth exceeds 256".into(),
            ));
        }
        Ok(())
    }
    pub fn parameters(&mut self, params: &[Type]) -> Result<(Vec<Id>, Id), Failure> {
        let mut values = Vec::new();
        let mut domain = Vec::new();
        for (i, ty) in params.iter().enumerate() {
            let value = if *ty == Type::Unit {
                self.arena.int("0")?
            } else {
                self.arena.add(sort(*ty), format!("p{i}"))?
            };
            if *ty == Type::I64 {
                domain.push(self.arena.range(value)?);
            }
            values.push(value);
        }
        Ok((values, self.arena.and(&domain)?))
    }
    pub fn spec(
        &mut self,
        expr: &SpecExpr,
        params: &[Id],
        result: Option<Id>,
        depth: usize,
    ) -> Result<Symbolic, Failure> {
        self.visit(depth)?;
        let pure = |value, safe| Symbolic { value, safe };
        let safe = self.arena.truth()?;
        Ok(match &expr.kind {
            SpecExprKind::Integer(n) => pure(self.arena.int(n)?, safe),
            SpecExprKind::Boolean(b) => pure(self.arena.bool(*b)?, safe),
            SpecExprKind::Unit => pure(self.arena.int("0")?, safe),
            SpecExprKind::Param(i) => pure(
                *params
                    .get(*i)
                    .ok_or_else(|| Failure::Error("invalid checked contract parameter".into()))?,
                safe,
            ),
            SpecExprKind::Result => pure(
                result.ok_or_else(|| Failure::Error("result outside postcondition".into()))?,
                safe,
            ),
            SpecExprKind::Unary { op, operand } => {
                let a = self.spec(operand, params, result, depth + 1)?;
                self.unary(*op, a, false)?
            }
            SpecExprKind::Binary { op, left, right } => {
                let a = self.spec(left, params, result, depth + 1)?;
                let b = self.spec(right, params, result, depth + 1)?;
                self.binary(*op, a, b, spec_type(expr.ty), false)?
            }
        })
    }
    pub fn expr(&mut self, expr: &Expr, env: &[Id], depth: usize) -> Result<Symbolic, Failure> {
        self.visit(depth)?;
        let safe = self.arena.truth()?;
        Ok(match &expr.kind {
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
            ExprKind::Local(i) => Symbolic {
                value: *env
                    .get(*i)
                    .ok_or_else(|| Failure::Error("invalid checked local".into()))?,
                safe,
            },
            ExprKind::Let { value, body } => {
                let a = self.expr(value, env, depth + 1)?;
                let mut inner = Vec::with_capacity(env.len() + 1);
                inner.push(a.value);
                inner.extend_from_slice(env);
                let b = self.expr(body, &inner, depth + 1)?;
                Symbolic {
                    value: b.value,
                    safe: self.arena.and(&[a.safe, b.safe])?,
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let c = self.expr(condition, env, depth + 1)?;
                let a = self.expr(then_branch, env, depth + 1)?;
                let b = self.expr(else_branch, env, depth + 1)?;
                let yes = self.arena.implies(c.value, a.safe)?;
                let nc = self.arena.not(c.value)?;
                let no = self.arena.implies(nc, b.safe)?;
                Symbolic {
                    value: self.arena.add(
                        sort(expr.ty),
                        format!("(ite n{} n{} n{})", c.value, a.value, b.value),
                    )?,
                    safe: self.arena.and(&[c.safe, yes, no])?,
                }
            }
            ExprKind::Unary { op, operand } => {
                let a = self.expr(operand, env, depth + 1)?;
                self.unary(*op, a, true)?
            }
            ExprKind::Binary { op, left, right } => {
                let a = self.expr(left, env, depth + 1)?;
                let b = self.expr(right, env, depth + 1)?;
                self.binary(*op, a, b, expr.ty, true)?
            }
            ExprKind::Call {
                function,
                arguments,
            } => {
                let mut values = Vec::new();
                let mut conditions = Vec::new();
                for arg in arguments {
                    let a = self.expr(arg, env, depth + 1)?;
                    values.push(a.value);
                    conditions.push(a.safe);
                }
                let contracts = self
                    .program
                    .contracts
                    .as_ref()
                    .ok_or_else(|| Failure::Error("source contracts are absent".into()))?;
                for clause in &contracts[*function].requires {
                    let pre = self.spec(&clause.expr, &values, None, depth + 1)?;
                    conditions.extend([pre.safe, pre.value]);
                }
                values.reverse();
                let body =
                    self.expr(&self.program.functions[*function].body, &values, depth + 1)?;
                conditions.push(body.safe);
                Symbolic {
                    value: body.value,
                    safe: self.arena.and(&conditions)?,
                }
            }
        })
    }
    fn unary(&mut self, op: UnaryOp, a: Symbolic, machine: bool) -> Result<Symbolic, Failure> {
        let value = match op {
            UnaryOp::Not => self.arena.not(a.value)?,
            UnaryOp::Neg => self.arena.add("Int", format!("(- n{})", a.value))?,
        };
        let safe = if machine && op == UnaryOp::Neg {
            let bound = self.arena.range(value)?;
            self.arena.and(&[a.safe, bound])?
        } else {
            a.safe
        };
        Ok(Symbolic { value, safe })
    }
    fn binary(
        &mut self,
        op: BinaryOp,
        a: Symbolic,
        b: Symbolic,
        ty: Type,
        machine: bool,
    ) -> Result<Symbolic, Failure> {
        let x = a.value;
        let y = b.value;
        let body = match op {
            BinaryOp::Add => format!("(+ n{x} n{y})"),
            BinaryOp::Sub => format!("(- n{x} n{y})"),
            BinaryOp::Mul => format!("(* n{x} n{y})"),
            BinaryOp::Div => format!("(apl_div n{x} n{y})"),
            BinaryOp::Rem => format!("(- n{x} (* n{y} (apl_div n{x} n{y})))"),
            BinaryOp::Lt => format!("(< n{x} n{y})"),
            BinaryOp::Le => format!("(<= n{x} n{y})"),
            BinaryOp::Gt => format!("(> n{x} n{y})"),
            BinaryOp::Ge => format!("(>= n{x} n{y})"),
            BinaryOp::Eq => format!("(= n{x} n{y})"),
            BinaryOp::Ne => format!("(not (= n{x} n{y}))"),
            BinaryOp::And => format!("(and n{x} n{y})"),
            BinaryOp::Or => format!("(or n{x} n{y})"),
        };
        let value = self.arena.add(sort(ty), body)?;
        let mut conditions = vec![a.safe];
        match op {
            BinaryOp::And => conditions.push(self.arena.implies(x, b.safe)?),
            BinaryOp::Or => {
                let nx = self.arena.not(x)?;
                conditions.push(self.arena.implies(nx, b.safe)?);
            }
            _ => conditions.push(b.safe),
        }
        if matches!(op, BinaryOp::Div | BinaryOp::Rem) {
            conditions.push(self.arena.add("Bool", format!("(not (= n{y} 0))"))?);
            if machine {
                conditions.push(self.arena.add(
                    "Bool",
                    format!("(not (and (= n{x} (- 9223372036854775808)) (= n{y} (- 1))))"),
                )?);
            }
        } else if machine && matches!(op, BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul) {
            conditions.push(self.arena.range(value)?);
        }
        Ok(Symbolic {
            value,
            safe: self.arena.and(&conditions)?,
        })
    }
}

pub(super) fn acyclic(program: &Program) -> Result<(), Failure> {
    let n = program.functions.len();
    let mut edges = vec![Vec::new(); n];
    let mut indegree = vec![0; n];
    let mut count = 0;
    for (i, function) in program.functions.iter().enumerate() {
        let mut work = vec![&function.body];
        while let Some(expr) = work.pop() {
            count += 1;
            if count > MAX_NODES {
                return Err(Failure::Unknown(
                    "program expression count exceeds 100000".into(),
                ));
            }
            match &expr.kind {
                ExprKind::Call {
                    function,
                    arguments,
                } => {
                    edges[i].push(*function);
                    indegree[*function] += 1;
                    work.extend(arguments);
                }
                ExprKind::Let { value, body } => work.extend([value.as_ref(), body.as_ref()]),
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => work.extend([
                    condition.as_ref(),
                    then_branch.as_ref(),
                    else_branch.as_ref(),
                ]),
                ExprKind::Unary { operand, .. } => work.push(operand),
                ExprKind::Binary { left, right, .. } => {
                    work.extend([left.as_ref(), right.as_ref()])
                }
                _ => {}
            }
        }
    }
    let mut ready: Vec<_> = (0..n).filter(|i| indegree[*i] == 0).collect();
    let mut visited = 0;
    while let Some(i) = ready.pop() {
        visited += 1;
        for &j in &edges[i] {
            indegree[j] -= 1;
            if indegree[j] == 0 {
                ready.push(j);
            }
        }
    }
    if visited != n {
        return Err(Failure::Unsupported(
            "recursive function calls are outside apl-verify-v0".into(),
        ));
    }
    Ok(())
}

pub(super) struct Pending {
    pub kind: &'static str,
    pub span: Span,
    pub assertion: Id,
    pub expected_sat: bool,
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
    let env: Vec<_> = params.iter().rev().copied().collect();
    let body = genr.expr(&f.body, &env, 0)?;
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
