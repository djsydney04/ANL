use super::{Failure, MAX_NODES, MAX_QUERY_BYTES};
use crate::{
    diagnostic::Span,
    types::{BinaryOp, Expr, ExprKind, Program, SpecExpr, SpecExprKind, SpecType, Type, UnaryOp},
};
use std::{fmt::Write, time::Instant};

pub(super) type Id = usize;
#[derive(Clone, Copy)]
pub(super) struct Symbolic {
    pub value: Id,
    pub safe: Id,
}
struct Node {
    sort: &'static str,
    body: String,
    links: Option<Links>,
}
#[derive(Clone, Copy)]
pub(super) enum SymbolRef {
    Parameter,
    Head(usize),
}
enum Operands {
    None,
    One(Id),
    Two([Id; 2]),
    Three([Id; 3]),
    Many(Box<[Id]>),
}
impl Operands {
    fn ids(&self) -> &[Id] {
        match self {
            Self::None => &[],
            Self::One(id) => std::slice::from_ref(id),
            Self::Two(ids) => ids,
            Self::Three(ids) => ids,
            Self::Many(ids) => ids,
        }
    }
}
struct Links {
    operands: Operands,
    symbol: Option<SymbolRef>,
}
pub(super) const MAX_SYMBOLIC_WORK: usize = 1_000_000;
pub(super) const MAX_ARENA_NODES: usize = 100_000;

pub(super) struct StateBudget {
    work: usize,
    nodes: usize,
    deadline: Instant,
    pub heads: usize,
    pub occurrences: usize,
    pub expansions: usize,
    pub pending_queries: usize,
}
impl StateBudget {
    pub fn new(deadline: Instant) -> Self {
        Self {
            work: 0,
            nodes: 0,
            deadline,
            heads: 0,
            occurrences: 0,
            expansions: 0,
            pending_queries: 0,
        }
    }
    pub fn usage(&self) -> serde_json::Value {
        serde_json::json!({"symbolic_work":self.work,"arena_nodes":self.nodes,"head_symbols":self.heads,"loop_occurrences":self.occurrences,"expansions":self.expansions,"pending_queries":self.pending_queries})
    }
    pub fn charge(&mut self, amount: usize) -> Result<(), Failure> {
        if Instant::now() >= self.deadline {
            return Err(Failure::Unknown(
                "verification deadline exceeded during symbolic analysis".into(),
            ));
        }
        self.work = self
            .work
            .checked_add(amount)
            .filter(|n| *n <= MAX_SYMBOLIC_WORK)
            .ok_or_else(|| Failure::Unknown("symbolic work exceeds 1000000 units".into()))?;
        Ok(())
    }
    pub fn reserve<T>(&mut self, values: &mut Vec<T>, additional: usize) -> Result<(), Failure> {
        let needed = values
            .len()
            .checked_add(additional)
            .ok_or_else(|| Failure::Unknown("symbolic allocation size overflow".into()))?;
        if needed > values.capacity() {
            let capacity = needed
                .checked_next_power_of_two()
                .ok_or_else(|| Failure::Unknown("symbolic allocation size overflow".into()))?;
            self.charge(
                capacity
                    .checked_add(values.len())
                    .ok_or_else(|| Failure::Unknown("symbolic allocation size overflow".into()))?,
            )?;
            values
                .try_reserve_exact(capacity - values.len())
                .map_err(|_| Failure::Unknown("symbolic allocation failed".into()))?;
        }
        self.charge(additional)
    }
}

pub(super) struct Arena<'a> {
    nodes: Vec<Node>,
    bytes: usize,
    budget: Option<&'a mut StateBudget>,
    tracking: bool,
    heads: Vec<(usize, Type)>,
    marks: Vec<usize>,
    traversal: usize,
    pub product_parameters: Option<ParameterPlan>,
}
impl Arena<'_> {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            bytes: 0,
            budget: None,
            tracking: false,
            heads: Vec::new(),
            marks: Vec::new(),
            traversal: 0,
            product_parameters: None,
        }
    }
    pub fn work(&mut self, amount: usize) -> Result<(), Failure> {
        if let Some(budget) = &mut self.budget {
            budget.charge(amount)?;
        }
        Ok(())
    }
    pub fn add(&mut self, sort: &'static str, body: String) -> Result<Id, Failure> {
        if self.tracking {
            return Err(Failure::Error("untracked loop formula insertion".into()));
        }
        self.insert(sort, body, None)
    }
    pub fn reserve<T>(&mut self, values: &mut Vec<T>, additional: usize) -> Result<(), Failure> {
        self.budget
            .as_deref_mut()
            .ok_or_else(|| Failure::Error("missing symbolic budget".into()))?
            .reserve(values, additional)
    }
    pub fn budget(&mut self) -> Result<&mut StateBudget, Failure> {
        self.budget
            .as_deref_mut()
            .ok_or_else(|| Failure::Error("missing symbolic budget".into()))
    }
    pub fn tracking(&mut self) {
        self.tracking = true;
    }
    pub(super) fn leaf(
        &mut self,
        sort: &'static str,
        body: String,
        symbol: Option<SymbolRef>,
    ) -> Result<Id, Failure> {
        let links = self.tracking.then_some(Links {
            operands: Operands::None,
            symbol,
        });
        self.insert(sort, body, links)
    }
    pub fn app(&mut self, sort: &'static str, body: String, ids: &[Id]) -> Result<Id, Failure> {
        let links = if self.tracking {
            self.work(ids.len())?;
            let operands = match ids {
                [] => Operands::None,
                [a] => Operands::One(*a),
                [a, b] => Operands::Two([*a, *b]),
                [a, b, c] => Operands::Three([*a, *b, *c]),
                _ => {
                    self.work(ids.len())?;
                    Operands::Many(ids.into())
                }
            };
            Some(Links {
                operands,
                symbol: None,
            })
        } else {
            None
        };
        self.insert(sort, body, links)
    }
    fn insert(
        &mut self,
        sort: &'static str,
        body: String,
        links: Option<Links>,
    ) -> Result<Id, Failure> {
        self.work(1)?;
        if let Some(budget) = &mut self.budget {
            if budget.nodes >= MAX_ARENA_NODES {
                return Err(Failure::Unknown(
                    "symbolic arena exceeds 100000 nodes".into(),
                ));
            }
            budget.nodes += 1;
        }
        self.bytes += if self.budget.is_some() {
            definition_bytes(self.nodes.len(), sort, body.len())
        } else {
            format!("(define-fun n{} () {sort} {body})\n", self.nodes.len()).len()
        };
        if self.bytes > MAX_QUERY_BYTES {
            return Err(Failure::Unknown(
                "generated query exceeds 1048576 bytes".into(),
            ));
        }
        let id = self.nodes.len();
        if self.tracking {
            self.budget
                .as_deref_mut()
                .expect("tracking budget")
                .reserve(&mut self.nodes, 1)?;
        }
        self.nodes.push(Node { sort, body, links });
        Ok(id)
    }
    pub fn head(&mut self, ty: Type) -> Result<(usize, Id), Failure> {
        if ty == Type::Unit {
            return Err(Failure::Error(
                "unit cannot allocate a loop head symbol".into(),
            ));
        }
        let budget = self.budget()?;
        if budget.heads >= 4096 {
            return Err(Failure::Unknown("loop heads exceed 4096 symbols".into()));
        }
        let head = budget.heads;
        budget.heads += 1;
        self.budget
            .as_deref_mut()
            .expect("head budget")
            .reserve(&mut self.heads, 1)?;
        self.heads.push((head, ty));
        let id = self.leaf(sort(ty)?, format!("h{head}"), Some(SymbolRef::Head(head)))?;
        Ok((head, id))
    }
    pub fn relevant_heads(&mut self, root: Id) -> Result<Vec<usize>, Failure> {
        let missing = self.nodes.len() - self.marks.len();
        if missing > 0 {
            self.budget
                .as_deref_mut()
                .expect("dependency budget")
                .reserve(&mut self.marks, missing)?;
            self.marks.resize(self.nodes.len(), 0);
        }
        self.traversal = self
            .traversal
            .checked_add(1)
            .ok_or_else(|| Failure::Unknown("dependency traversal count overflow".into()))?;
        let mut stack = Vec::new();
        let mut heads = Vec::new();
        self.reserve(&mut stack, 1)?;
        stack.push(root);
        *self
            .marks
            .get_mut(root)
            .ok_or_else(|| Failure::Error("invalid query root".into()))? = self.traversal;
        while let Some(id) = stack.pop() {
            self.work(1)?;
            let links = self.nodes[id]
                .links
                .as_ref()
                .ok_or_else(|| Failure::Error("missing formula dependencies".into()))?;
            let symbol = links.symbol;
            let count = links.operands.ids().len();
            if let Some(SymbolRef::Head(head)) = symbol {
                self.reserve(&mut heads, 1)?;
                heads.push(head);
            }
            for index in 0..count {
                self.work(1)?;
                let child = self.nodes[id].links.as_ref().expect("links").operands.ids()[index];
                if child >= id {
                    return Err(Failure::Error("nonpreceding formula dependency".into()));
                }
                if self.marks[child] != self.traversal {
                    self.marks[child] = self.traversal;
                    self.reserve(&mut stack, 1)?;
                    stack.push(child);
                }
            }
        }
        self.work(heads.len().saturating_mul(13))?;
        heads.sort_unstable();
        heads.dedup();
        Ok(heads)
    }
    pub fn truth(&mut self) -> Result<Id, Failure> {
        self.leaf("Bool", "true".into(), None)
    }
    pub fn bool(&mut self, value: bool) -> Result<Id, Failure> {
        self.leaf("Bool", value.to_string(), None)
    }
    pub fn int(&mut self, value: &str) -> Result<Id, Failure> {
        if self.budget.is_some()
            && definition_bytes(self.nodes.len(), "Int", value.len())
                > MAX_QUERY_BYTES.saturating_sub(self.bytes)
        {
            return Err(Failure::Unknown(
                "generated query exceeds 1048576 bytes".into(),
            ));
        }
        self.leaf("Int", value.into(), None)
    }
    pub fn and(&mut self, ids: &[Id]) -> Result<Id, Failure> {
        self.work(ids.len())?;
        if ids.is_empty() {
            return self.truth();
        }
        if ids.len() == 1 {
            return Ok(ids[0]);
        }
        if self.budget.is_some() {
            let mut length = 5;
            for id in ids {
                self.work(0)?;
                length += 3 + id.checked_ilog10().unwrap_or(0) as usize;
            }
            if definition_bytes(self.nodes.len(), "Bool", length)
                > MAX_QUERY_BYTES.saturating_sub(self.bytes)
            {
                return Err(Failure::Unknown(
                    "generated query exceeds 1048576 bytes".into(),
                ));
            }
            self.work(ids.len())?;
            let mut body = String::with_capacity(length);
            body.push_str("(and");
            for id in ids {
                self.work(0)?;
                write!(body, " n{id}").expect("String write");
            }
            body.push(')');
            return self.app("Bool", body, ids);
        }
        self.app(
            "Bool",
            format!(
                "(and {})",
                ids.iter()
                    .map(|id| format!("n{id}"))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            ids,
        )
    }
    pub fn not(&mut self, id: Id) -> Result<Id, Failure> {
        self.app("Bool", format!("(not n{id})"), &[id])
    }
    pub fn implies(&mut self, a: Id, b: Id) -> Result<Id, Failure> {
        self.app("Bool", format!("(=> n{a} n{b})"), &[a, b])
    }
    pub fn range(&mut self, id: Id) -> Result<Id, Failure> {
        self.app(
            "Bool",
            format!("(and (<= (- 9223372036854775808) n{id}) (<= n{id} 9223372036854775807))"),
            &[id],
        )
    }
    pub fn render(
        &mut self,
        params: &[Type],
        assertion: Id,
        timeout_ms: u128,
    ) -> Result<String, Failure> {
        let product = self.product_parameters.is_some();
        let timeout_ms = timeout_ms.max(1);
        let prefix = "(set-option :print-success false)\n(set-option :produce-models true)\n(set-option :timeout ";
        if product {
            self.work(prefix.len() + timeout_ms.ilog10() as usize + 3)?;
        }
        let mut text = format!("{prefix}{timeout_ms})\n");
        let arithmetic = "(define-fun apl_abs ((x Int)) Int (ite (< x 0) (- x) x))\n(define-fun apl_div ((a Int) (b Int)) Int (ite (= b 0) 0 (ite (= (< a 0) (< b 0)) (div (apl_abs a) (apl_abs b)) (- (div (apl_abs a) (apl_abs b))))))\n";
        if product {
            self.work(arithmetic.len())?;
        }
        text.push_str(arithmetic);
        self.work(params.len())?;
        if let Some(plan) = &self.product_parameters {
            let count = plan.leaves.len();
            for index in 0..count {
                self.work(1)?;
                let leaf = self
                    .product_parameters
                    .as_ref()
                    .expect("parameter plan")
                    .leaves[index];
                if leaf.ty != Type::Unit {
                    let declaration =
                        format!("(declare-const {} {})\n", leaf.name(), sort(leaf.ty)?);
                    self.work(declaration.len())?;
                    if text.len() + declaration.len() > MAX_QUERY_BYTES {
                        return Err(Failure::Unknown(
                            "generated query exceeds 1048576 bytes".into(),
                        ));
                    }
                    text.push_str(&declaration);
                }
            }
        } else {
            for (i, ty) in params.iter().enumerate() {
                if let Some(budget) = &mut self.budget {
                    budget.charge(0)?;
                }
                if *ty != Type::Unit {
                    let declaration = format!("(declare-const p{i} {})\n", sort(*ty)?);
                    if self.budget.is_some() && text.len() + declaration.len() > MAX_QUERY_BYTES {
                        return Err(Failure::Unknown(
                            "generated query exceeds 1048576 bytes".into(),
                        ));
                    }
                    text.push_str(&declaration);
                }
            }
        }
        for i in 0..self.heads.len() {
            self.work(1)?;
            let (id, ty) = self.heads[i];
            let declaration = format!("(declare-const h{id} {})\n", sort(ty)?);
            if product {
                self.work(declaration.len())?;
            }
            if text.len() + declaration.len() > MAX_QUERY_BYTES {
                return Err(Failure::Unknown(
                    "generated query exceeds 1048576 bytes".into(),
                ));
            }
            text.push_str(&declaration);
        }
        for (i, node) in self.nodes.iter().enumerate() {
            if let Some(budget) = &mut self.budget {
                budget.charge(if product {
                    definition_bytes(i, node.sort, node.body.len())
                } else {
                    0
                })?;
                if text.len() + definition_bytes(i, node.sort, node.body.len()) > MAX_QUERY_BYTES {
                    return Err(Failure::Unknown(
                        "generated query exceeds 1048576 bytes".into(),
                    ));
                }
            }
            text.push_str(&format!(
                "(define-fun n{i} () {} {})\n",
                node.sort, node.body
            ));
        }
        let ending = format!("(assert n{assertion})\n(check-sat)\n");
        if product {
            self.work(ending.len())?;
        }
        if self.budget.is_some() && text.len() + ending.len() > MAX_QUERY_BYTES {
            return Err(Failure::Unknown(
                "generated query exceeds 1048576 bytes".into(),
            ));
        }
        text.push_str(&ending);
        if text.len() > MAX_QUERY_BYTES {
            return Err(Failure::Unknown(
                "generated query exceeds 1048576 bytes".into(),
            ));
        }
        Ok(text)
    }
}
fn definition_bytes(id: usize, sort: &str, body_bytes: usize) -> usize {
    format!("(define-fun n{id} () {sort} )\n").len() + body_bytes
}
pub(super) fn sort(ty: Type) -> Result<&'static str, Failure> {
    match ty {
        Type::Bool => Ok("Bool"),
        Type::I64 | Type::Unit => Ok("Int"),
        Type::Tuple(_) => Err(Failure::Error("product reached scalar SMT sort".into())),
    }
}

fn spec_type(ty: SpecType) -> Type {
    match ty {
        SpecType::Int => Type::I64,
        SpecType::Bool => Type::Bool,
        SpecType::Unit => Type::Unit,
        SpecType::Tuple(_) => unreachable!("product reached scalar specification generator"),
    }
}

pub(super) struct Generator<'a> {
    pub arena: Arena<'a>,
    pub(super) program: &'a Program,
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
    pub fn with_state_budget(
        program: &'a Program,
        expanded: &'a mut usize,
        budget: &'a mut StateBudget,
    ) -> Self {
        Self {
            arena: Arena {
                nodes: Vec::new(),
                bytes: 0,
                budget: Some(budget),
                tracking: false,
                heads: Vec::new(),
                marks: Vec::new(),
                traversal: 0,
                product_parameters: None,
            },
            program,
            expanded,
        }
    }
    pub(super) fn visit(&mut self, depth: usize) -> Result<(), Failure> {
        self.arena.work(0)?;
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
        self.arena.work(params.len())?;
        let mut values = Vec::new();
        let mut domain = Vec::new();
        if self.arena.tracking {
            self.arena.reserve(&mut values, params.len())?;
            self.arena.reserve(&mut domain, params.len())?;
        }
        for (i, ty) in params.iter().enumerate() {
            let value = if *ty == Type::Unit {
                self.arena.int("0")?
            } else {
                self.arena
                    .leaf(sort(*ty)?, format!("p{i}"), Some(SymbolRef::Parameter))?
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
            SpecExprKind::Tuple(_) | SpecExprKind::Project { .. } => {
                return Err(Failure::Error(
                    "product reached scalar specification generator".into(),
                ));
            }
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
            ExprKind::Memory(_) => {
                return Err(Failure::Unsupported(
                    "buffers and views are not supported".into(),
                ));
            }
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
            ExprKind::Local(i) => Symbolic {
                value: *env
                    .get(*i)
                    .ok_or_else(|| Failure::Error("invalid checked local".into()))?,
                safe,
            },
            ExprKind::LetMut { .. } | ExprKind::Assign { .. } | ExprKind::While { .. } => {
                return Err(Failure::Unsupported(
                    "local state is outside apl-verify-v0".into(),
                ));
            }
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
                        sort(expr.ty)?,
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
    pub(super) fn unary(
        &mut self,
        op: UnaryOp,
        a: Symbolic,
        machine: bool,
    ) -> Result<Symbolic, Failure> {
        let value = match op {
            UnaryOp::Not => self.arena.not(a.value)?,
            UnaryOp::Neg => self
                .arena
                .app("Int", format!("(- n{})", a.value), &[a.value])?,
        };
        let safe = if machine && op == UnaryOp::Neg {
            let bound = self.arena.range(value)?;
            self.arena.and(&[a.safe, bound])?
        } else {
            a.safe
        };
        Ok(Symbolic { value, safe })
    }
    pub(super) fn binary(
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
        let value = self.arena.app(sort(ty)?, body, &[x, y])?;
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
            conditions.push(self.arena.app("Bool", format!("(not (= n{y} 0))"), &[y])?);
            if machine {
                conditions.push(self.arena.app(
                    "Bool",
                    format!("(not (and (= n{x} (- 9223372036854775808)) (= n{y} (- 1))))"),
                    &[x, y],
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

pub(super) fn supported(program: &Program) -> Result<(), Failure> {
    for function in &program.functions {
        let mut work = vec![&function.body];
        while let Some(expr) = work.pop() {
            let construct = match &expr.kind {
                ExprKind::Memory(_) => Some("buffers and views"),
                ExprKind::Tuple(_) | ExprKind::Project { .. } => Some("flat products"),
                ExprKind::While { .. } => Some("while"),
                ExprKind::Assign { value, .. } => {
                    work.push(value);
                    None
                }
                ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                    work.extend([body.as_ref(), value.as_ref()]);
                    None
                }
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    work.extend([
                        else_branch.as_ref(),
                        then_branch.as_ref(),
                        condition.as_ref(),
                    ]);
                    None
                }
                ExprKind::Unary { operand, .. } => {
                    work.push(operand);
                    None
                }
                ExprKind::Binary { left, right, .. } => {
                    work.extend([right.as_ref(), left.as_ref()]);
                    None
                }
                ExprKind::Call { arguments, .. } => {
                    work.extend(arguments.iter().rev());
                    None
                }
                ExprKind::Integer(_)
                | ExprKind::Boolean(_)
                | ExprKind::Unit
                | ExprKind::Local(_) => None,
            };
            if let Some(construct) = construct {
                return Err(Failure::Unsupported(format!(
                    "{construct} in function {} is outside apl-state-verify-v1; loops are not verified",
                    function.name
                )));
            }
        }
    }
    Ok(())
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
                ExprKind::Tuple(fields) => work.extend(fields),
                ExprKind::Project { value, .. } => work.push(value),
                ExprKind::While { condition, body } => {
                    work.extend([condition.as_ref(), body.as_ref()])
                }
                ExprKind::Call {
                    function,
                    arguments,
                } => {
                    edges[i].push(*function);
                    indegree[*function] += 1;
                    work.extend(arguments);
                }
                ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                    work.extend([value.as_ref(), body.as_ref()])
                }
                ExprKind::Assign { value, .. } => work.push(value),
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
        return Err(Failure::Unsupported(format!(
            "recursive function calls are outside {}",
            if program.has_local_state() {
                "apl-state-verify-v1"
            } else {
                "apl-verify-v0"
            }
        )));
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

#[derive(Clone, Copy)]
pub(super) struct ParameterLeaf {
    pub parameter: usize,
    pub field: Option<usize>,
    pub logical_id: usize,
    pub ty: Type,
}
impl ParameterLeaf {
    pub fn name(self) -> String {
        match self.field {
            Some(field) => format!("p{}_f{field}", self.parameter),
            None => format!("p{}", self.parameter),
        }
    }
    pub fn origin(self) -> serde_json::Value {
        let mut origin = serde_json::json!({"kind":"parameter","index":self.parameter,"logical_id":self.logical_id});
        if let Some(field) = self.field {
            origin["field_index"] = serde_json::json!(field);
        }
        origin
    }
}
pub(super) struct ParameterPlan {
    pub leaves: Vec<ParameterLeaf>,
    pub slots: usize,
    pub head_display_start: usize,
}
impl ParameterPlan {
    pub fn new(params: &[Type], budget: &mut StateBudget) -> Result<Self, Failure> {
        let mut leaves = Vec::new();
        let mut slots = 0;
        for (parameter, ty) in params.iter().enumerate() {
            budget.charge(1)?;
            match ty {
                Type::Tuple(shape) => {
                    budget.reserve(&mut leaves, shape.fields().len())?;
                    for (field, ty) in shape.fields().iter().enumerate() {
                        budget.charge(1)?;
                        leaves.push(ParameterLeaf {
                            parameter,
                            field: Some(field),
                            logical_id: slots,
                            ty: ty.as_type(),
                        });
                        slots += 1;
                    }
                }
                _ => {
                    budget.reserve(&mut leaves, 1)?;
                    leaves.push(ParameterLeaf {
                        parameter,
                        field: None,
                        logical_id: slots,
                        ty: *ty,
                    });
                    slots += 1;
                }
            }
        }
        Ok(Self {
            leaves,
            slots,
            head_display_start: budget.heads,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn state_arena_node_limit_is_shared_across_function_arenas() {
        let mut budget = StateBudget::new(Instant::now() + Duration::from_secs(5));
        budget.nodes = MAX_ARENA_NODES - 1;
        let mut first = Arena {
            nodes: Vec::new(),
            bytes: 0,
            budget: Some(&mut budget),
            tracking: false,
            heads: Vec::new(),
            marks: Vec::new(),
            traversal: 0,
            product_parameters: None,
        };
        assert!(first.truth().is_ok());
        drop(first);
        let mut second = Arena {
            nodes: Vec::new(),
            bytes: 0,
            budget: Some(&mut budget),
            tracking: false,
            heads: Vec::new(),
            marks: Vec::new(),
            traversal: 0,
            product_parameters: None,
        };
        assert!(
            matches!(second.truth(), Err(Failure::Unknown(message)) if message.contains("arena"))
        );
        assert!(second.nodes.is_empty());
    }

    #[test]
    fn state_operand_budget_is_reserved_before_building_a_formula() {
        let mut budget = StateBudget::new(Instant::now() + Duration::from_secs(5));
        let mut arena = Arena {
            nodes: Vec::new(),
            bytes: 0,
            budget: Some(&mut budget),
            tracking: false,
            heads: Vec::new(),
            marks: Vec::new(),
            traversal: 0,
            product_parameters: None,
        };
        let value = arena.truth().unwrap();
        arena.budget.as_mut().unwrap().work = MAX_SYMBOLIC_WORK - 1;
        assert!(
            matches!(arena.and(&[value, value]), Err(Failure::Unknown(message)) if message.contains("symbolic work"))
        );
        assert_eq!(arena.nodes.len(), 1);
    }

    #[test]
    fn head_allocation_is_attempt_wide_and_rejects_before_insertion() {
        let mut budget = StateBudget::new(Instant::now() + Duration::from_secs(5));
        budget.heads = 4095;
        let mut first = Arena::new();
        first.budget = Some(&mut budget);
        first.tracking();
        assert_eq!(first.head(Type::Bool).unwrap().0, 4095);
        assert!(first.head(Type::Unit).is_err());
        drop(first);
        let mut second = Arena::new();
        second.budget = Some(&mut budget);
        second.tracking();
        assert!(
            matches!(second.head(Type::I64),Err(Failure::Unknown(message)) if message.contains("4096"))
        );
        assert!(second.nodes.is_empty());
        assert!(second.heads.is_empty());
    }

    #[test]
    fn dependency_closure_is_exact_and_raw_insertions_cannot_bypass_it() {
        let mut budget = StateBudget::new(Instant::now() + Duration::from_secs(5));
        let mut arena = Arena::new();
        arena.budget = Some(&mut budget);
        arena.tracking();
        let (_, first) = arena.head(Type::I64).unwrap();
        let (_, second) = arena.head(Type::Bool).unwrap();
        let compare = arena
            .app("Bool", format!("(= n{first} 0)"), &[first])
            .unwrap();
        let unrelated = arena.not(second).unwrap();
        assert_eq!(arena.relevant_heads(compare).unwrap(), vec![0]);
        assert_eq!(arena.relevant_heads(unrelated).unwrap(), vec![1]);
        let both = arena.and(&[compare, unrelated]).unwrap();
        assert_eq!(arena.relevant_heads(both).unwrap(), vec![0, 1]);
        let length = arena.nodes.len();
        assert!(matches!(
            arena.add("Bool", "true".into()),
            Err(Failure::Error(_))
        ));
        assert_eq!(arena.nodes.len(), length);
        arena.budget.as_mut().unwrap().work = MAX_SYMBOLIC_WORK;
        assert!(matches!(
            arena.relevant_heads(compare),
            Err(Failure::Unknown(_))
        ));
    }

    #[test]
    fn loop_formula_byte_and_operand_bounds_precede_node_insertion() {
        let mut budget = StateBudget::new(Instant::now() + Duration::from_secs(5));
        let mut arena = Arena::new();
        arena.budget = Some(&mut budget);
        arena.tracking();
        let id = arena.truth().unwrap();
        arena.bytes = MAX_QUERY_BYTES;
        assert!(
            matches!(arena.int("1"),Err(Failure::Unknown(message)) if message.contains("query"))
        );
        assert_eq!(arena.nodes.len(), 1);
        arena.bytes = 0;
        arena.budget.as_mut().unwrap().work = MAX_SYMBOLIC_WORK - 1;
        assert!(
            matches!(arena.and(&[id,id,id,id]),Err(Failure::Unknown(message)) if message.contains("work"))
        );
        assert_eq!(arena.nodes.len(), 1);
    }

    #[test]
    fn visits_depth_and_deadline_fail_closed_on_the_loop_route() {
        let program = crate::compile("fn f()->unit{while(true) invariant true;{}}").unwrap();
        let mut expanded = MAX_NODES;
        let mut budget = StateBudget::new(Instant::now() + Duration::from_secs(5));
        let mut generator = Generator::with_state_budget(&program, &mut expanded, &mut budget);
        generator.arena.tracking();
        assert!(
            matches!(generator.visit(0),Err(Failure::Unknown(message)) if message.contains("100000"))
        );
        *generator.expanded = 0;
        assert!(
            matches!(generator.visit(257),Err(Failure::Unknown(message)) if message.contains("depth"))
        );
        generator.arena.budget.as_mut().unwrap().deadline = Instant::now();
        assert!(
            matches!(generator.arena.truth(),Err(Failure::Unknown(message)) if message.contains("deadline"))
        );
        assert!(generator.arena.nodes.is_empty());
    }
}
