use crate::{
    MAX_EVAL_DEPTH,
    diagnostic::Span,
    types::{
        BinaryOp, Expr, ExprKind, MAX_TUPLE_FIELDS, MemoryExpr, Program, ResourceMode, ScalarType,
        TupleError, TupleShape, Type, UnaryOp, ViewMode,
    },
};
use std::{fmt, sync::Arc};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarValue {
    Integer(i64),
    Boolean(bool),
    Unit,
}
impl ScalarValue {
    pub fn ty(self) -> ScalarType {
        match self {
            Self::Integer(_) => ScalarType::I64,
            Self::Boolean(_) => ScalarType::Bool,
            Self::Unit => ScalarType::Unit,
        }
    }
    pub fn as_value(self) -> Value {
        match self {
            Self::Integer(n) => Value::Integer(n),
            Self::Boolean(b) => Value::Boolean(b),
            Self::Unit => Value::Unit,
        }
    }
}
/// Immutable, validated flat tuple payload. Copies share immutable storage only.
///
/// ```compile_fail,E0451
/// let tuple = anl::eval::TupleValue { fields: std::sync::Arc::from([]) };
/// ```
#[derive(Clone, PartialEq, Eq)]
pub struct TupleValue {
    fields: Arc<TuplePayload>,
}
#[derive(Debug, PartialEq, Eq)]
struct TuplePayload {
    fields: [ScalarValue; MAX_TUPLE_FIELDS],
    len: u8,
}
impl fmt::Debug for TupleValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TupleValue")
            .field("fields", &self.fields())
            .finish()
    }
}
impl TupleValue {
    pub fn new(fields: &[ScalarValue]) -> Result<Self, TupleError> {
        if !(1..=MAX_TUPLE_FIELDS).contains(&fields.len()) {
            return Err(TupleError);
        }
        let mut payload = TuplePayload {
            fields: [ScalarValue::Unit; MAX_TUPLE_FIELDS],
            len: fields.len() as u8,
        };
        payload.fields[..fields.len()].copy_from_slice(fields);
        Ok(Self {
            fields: Arc::new(payload),
        })
    }
    pub fn fields(&self) -> &[ScalarValue] {
        &self.fields.fields[..usize::from(self.fields.len)]
    }
    pub fn shape(&self) -> TupleShape {
        let mut fields = [ScalarType::Unit; MAX_TUPLE_FIELDS];
        for (i, value) in self.fields().iter().enumerate() {
            fields[i] = value.ty();
        }
        TupleShape::new(&fields[..self.fields().len()]).expect("validated tuple width")
    }
}

/// Executable values. Flat-product support changes this host type from Copy to
/// Clone; `ty` borrows, and tuple clones share an immutable validated payload.
#[derive(Debug, PartialEq, Eq)]
pub enum Value {
    Integer(i64),
    Boolean(bool),
    Unit,
    Tuple(TupleValue),
}
impl Clone for Value {
    #[inline(always)]
    fn clone(&self) -> Self {
        match self {
            Self::Integer(n) => Self::Integer(*n),
            Self::Boolean(b) => Self::Boolean(*b),
            Self::Unit => Self::Unit,
            Self::Tuple(value) => Self::Tuple(value.clone()),
        }
    }
}
impl Value {
    #[inline]
    fn has_type(&self, expected: &Type) -> bool {
        match (self, expected) {
            (Self::Integer(_), Type::I64)
            | (Self::Boolean(_), Type::Bool)
            | (Self::Unit, Type::Unit) => true,
            (Self::Tuple(value), Type::Tuple(shape)) => value.shape() == *shape,
            _ => false,
        }
    }
    #[inline]
    fn same_type(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Integer(_), Self::Integer(_))
            | (Self::Boolean(_), Self::Boolean(_))
            | (Self::Unit, Self::Unit) => true,
            (Self::Tuple(a), Self::Tuple(b)) => a.shape() == b.shape(),
            _ => false,
        }
    }
    pub fn ty(&self) -> Type {
        match self {
            Self::Integer(_) => Type::I64,
            Self::Boolean(_) => Type::Bool,
            Self::Unit => Type::Unit,
            Self::Tuple(value) => Type::Tuple(value.shape()),
        }
    }
}
impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(n) => write!(f, "{n}"),
            Self::Boolean(b) => write!(f, "{b}"),
            Self::Unit => f.write_str("()"),
            Self::Tuple(value) => {
                f.write_str("(")?;
                for (i, field) in value.fields().iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", field.as_value())?;
                }
                if value.fields().len() == 1 {
                    f.write_str(",")?;
                }
                f.write_str(")")
            }
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Trap {
    InvalidLength,
    IndexOutOfBounds,
    ArithmeticOverflow,
    DivisionByZero,
}
impl Trap {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::InvalidLength => "invalid_length",
            Self::IndexOutOfBounds => "index_out_of_bounds",
            Self::ArithmeticOverflow => "arithmetic_overflow",
            Self::DivisionByZero => "division_by_zero",
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError {
    Infrastructure(String),
    Trap { kind: Trap, span: Span },
    ResourceLimit { reason: &'static str, span: Span },
    InvalidIr,
}

pub fn evaluate(program: &Program, entry: usize, fuel: u64) -> Result<Value, EvalError> {
    evaluate_inner(
        program,
        entry,
        fuel,
        #[cfg(feature = "memory-evidence")]
        None,
    )
}
#[cfg(feature = "memory-evidence")]
pub fn evaluate_evidence(
    program: &Program,
    entry: usize,
    fuel: u64,
    options: &crate::memory_evidence::EvidenceOptions,
) -> Result<Value, EvalError> {
    options
        .check_program(program)
        .map_err(EvalError::Infrastructure)?;
    evaluate_inner(program, entry, fuel, Some(options.session()?))
}
fn evaluate_inner(
    program: &Program,
    entry: usize,
    fuel: u64,
    #[cfg(feature = "memory-evidence")] evidence: Option<crate::memory_evidence::Session>,
) -> Result<Value, EvalError> {
    let function = program.functions.get(entry).ok_or(EvalError::InvalidIr)?;
    if function.view.is_some() || !function.params.is_empty() {
        return Err(EvalError::InvalidIr);
    }
    let mut evaluator = Evaluator {
        program,
        fuel,
        products: program.has_flat_products(),
        memory: program.has_memory(),
        buffers: Vec::new(),
        live_cells: 0,
        tuple_fields: 0,
        active_slots: 0,
        #[cfg(feature = "memory-evidence")]
        evidence,
    };
    let result = evaluator.expr(&function.body, &mut Vec::new(), &mut Vec::new(), entry, 0);
    #[cfg(feature = "memory-evidence")]
    if let Some(evidence) = evaluator.evidence.take() {
        return evidence.finish(result);
    }
    result
}

#[derive(Clone, Copy)]
struct Resource {
    storage: usize,
    mode: ResourceMode,
}
struct Call<'a> {
    function: usize,
    arguments: &'a [Expr],
    view: Option<(Resource, ViewMode)>,
}
struct Storage {
    cells: Vec<i64>,
}
struct Evaluator<'a> {
    #[cfg(feature = "memory-evidence")]
    evidence: Option<crate::memory_evidence::Session>,
    memory: bool,
    buffers: Vec<Storage>,
    live_cells: usize,

    program: &'a Program,
    fuel: u64,
    products: bool,
    tuple_fields: usize,
    active_slots: usize,
}
pub const MAX_TUPLE_ALLOCATION_FIELDS: usize = 1_048_576;
pub const MAX_ACTIVE_SLOTS: usize = 65_536;
impl Evaluator<'_> {
    fn reserve_slots(&mut self, count: usize, span: Span) -> Result<(), EvalError> {
        if self.products || self.memory {
            self.active_slots = self
                .active_slots
                .checked_add(count)
                .filter(|n| *n <= MAX_ACTIVE_SLOTS)
                .ok_or(EvalError::ResourceLimit {
                    reason: "active environment and argument slot limit exceeded",
                    span,
                })?;
        }
        Ok(())
    }
    fn release_slots(&mut self, count: usize) {
        if self.products || self.memory {
            self.active_slots -= count;
        }
    }
    fn construct(&mut self, fields: &[ScalarValue], span: Span) -> Result<Value, EvalError> {
        self.tuple_fields = self
            .tuple_fields
            .checked_add(fields.len())
            .filter(|n| *n <= MAX_TUPLE_ALLOCATION_FIELDS)
            .ok_or(EvalError::ResourceLimit {
                reason: "cumulative tuple allocation field limit exceeded",
                span,
            })?;
        Ok(Value::Tuple(
            TupleValue::new(fields).map_err(|_| EvalError::InvalidIr)?,
        ))
    }

    fn access(&self, resources: &[Resource], index: usize) -> Result<Resource, EvalError> {
        let position = resources
            .len()
            .checked_sub(index.checked_add(1).ok_or(EvalError::InvalidIr)?)
            .ok_or(EvalError::InvalidIr)?;
        let r = *resources.get(position).ok_or(EvalError::InvalidIr)?;
        if self.buffers.get(r.storage).is_none() {
            return Err(EvalError::InvalidIr);
        }
        Ok(r)
    }
    fn call(
        &mut self,
        call: Call<'_>,
        env: &mut Vec<Value>,
        resources: &mut Vec<Resource>,
        caller: usize,
        depth: usize,
        span: Span,
    ) -> Result<Value, EvalError> {
        let Call {
            function,
            arguments,
            view,
        } = call;
        let callee = self
            .program
            .functions
            .get(function)
            .ok_or(EvalError::InvalidIr)?;
        if callee.params.len() != arguments.len() || callee.view != view.map(|(_, mode)| mode) {
            return Err(EvalError::InvalidIr);
        }
        if view.is_some_and(|(r, m)| !r.mode.lends(m)) {
            return Err(EvalError::InvalidIr);
        }
        let slots = arguments
            .len()
            .checked_add(usize::from(view.is_some()))
            .ok_or(EvalError::InvalidIr)?;
        self.reserve_slots(slots, span)?;
        let result = (|| {
            let mut values = Vec::new();
            values.try_reserve_exact(arguments.len()).map_err(|_| {
                EvalError::Infrastructure("argument metadata allocation failed".into())
            })?;
            let mut inputs = Vec::new();
            if view.is_some() {
                inputs.try_reserve_exact(1).map_err(|_| {
                    EvalError::Infrastructure("view metadata allocation failed".into())
                })?;
            }
            for (argument, expected) in arguments.iter().zip(&callee.params) {
                let value = self.expr(argument, env, resources, caller, depth)?;
                if !value.has_type(expected) {
                    return Err(EvalError::InvalidIr);
                }
                values.push(value);
            }
            if let Some((r, mode)) = view {
                inputs.push(Resource {
                    storage: r.storage,
                    mode: mode.into(),
                });
            }
            self.expr(&callee.body, &mut values, &mut inputs, function, depth)
        })();
        self.release_slots(slots);
        result
    }
    fn memory_expr(
        &mut self,
        memory: &MemoryExpr,
        env: &mut Vec<Value>,
        resources: &mut Vec<Resource>,
        function: usize,
        depth: usize,
        span: Span,
    ) -> Result<Value, EvalError> {
        let trap = |kind| EvalError::Trap { kind, span };
        match memory {
            MemoryExpr::Heap {
                site: _site,
                length,
                initial,
                success,
                failure,
            } => {
                let Value::Integer(length) = self.expr(length, env, resources, function, depth)?
                else {
                    return Err(EvalError::InvalidIr);
                };
                if length < 0 {
                    return Err(trap(Trap::InvalidLength));
                }
                let Value::Integer(initial) =
                    self.expr(initial, env, resources, function, depth)?
                else {
                    return Err(EvalError::InvalidIr);
                };
                let profile = self
                    .program
                    .allocation_profile
                    .ok_or(EvalError::InvalidIr)?;
                if length as u64 > profile.max_cells() {
                    return self.expr(failure, env, resources, function, depth);
                }
                let cells = (self.live_cells as u64)
                    .checked_add(length as u64)
                    .filter(|n| *n <= crate::memory::MAX_LIVE_CELLS as u64)
                    .ok_or(EvalError::ResourceLimit {
                        reason: "live buffer cell limit exceeded",
                        span,
                    })?;
                // The logical cap fits every supported host; narrow only after checking it.
                let n = length as usize;
                let cells = cells as usize;
                let slots = self
                    .active_slots
                    .checked_add(1)
                    .filter(|n| *n <= MAX_ACTIVE_SLOTS)
                    .ok_or(EvalError::ResourceLimit {
                        reason: "active environment and argument slot limit exceeded",
                        span,
                    })?;
                let fuel =
                    self.fuel
                        .checked_sub(length as u64)
                        .ok_or(EvalError::ResourceLimit {
                            reason: "buffer attempted-fill fuel exhausted",
                            span,
                        })?;
                self.buffers.try_reserve(1).map_err(|_| {
                    EvalError::Infrastructure("owner metadata allocation failed".into())
                })?;
                resources.try_reserve(1).map_err(|_| {
                    EvalError::Infrastructure("resource metadata allocation failed".into())
                })?;
                self.live_cells = cells;
                self.active_slots = slots;
                self.fuel = fuel;
                #[cfg(feature = "memory-evidence")]
                let site = crate::memory_evidence::Site {
                    function,
                    heap: *_site,
                };
                #[cfg(feature = "memory-evidence")]
                let response = if n > 0 {
                    self.evidence
                        .as_ref()
                        .map(|e| e.response(site, n as u64))
                        .transpose()?
                        .flatten()
                } else {
                    None
                };
                #[cfg(not(feature = "memory-evidence"))]
                let response: Option<bool> = None;
                let mut values = Vec::new();
                let allocation_ok =
                    n == 0 || (response != Some(false) && values.try_reserve_exact(n).is_ok());
                if n > 0 && response == Some(true) && !allocation_ok {
                    return Err(EvalError::Infrastructure(
                        "forced allocation success could not obtain storage".into(),
                    ));
                }
                #[cfg(feature = "memory-evidence")]
                let trace_id = if let Some(e) = self.evidence.as_mut() {
                    Some(if n == 0 {
                        e.empty(site)?
                    } else {
                        e.request(site, n as u64, allocation_ok)?
                    })
                } else {
                    None
                };
                if !allocation_ok {
                    self.live_cells -= n;
                    self.release_slots(1);
                    return self.expr(failure, env, resources, function, depth);
                }
                values.resize(n, initial);
                let storage = self.buffers.len();
                self.buffers.push(Storage { cells: values });
                resources.push(Resource {
                    storage,
                    mode: ResourceMode::Owner,
                });
                let result = self.expr(success, env, resources, function, depth);
                #[cfg(feature = "memory-evidence")]
                let result = if result.is_ok()
                    && let (Some(e), Some(id)) = (self.evidence.as_mut(), trace_id)
                    && let Err(error) = e.close(site, id, n == 0)
                {
                    Err(error)
                } else {
                    result
                };
                resources.pop();
                self.buffers.pop();
                self.live_cells -= n;
                self.release_slots(1);
                result
            }
            MemoryExpr::Length { resource } => {
                let r = self.access(resources, *resource)?;
                Ok(Value::Integer(self.buffers[r.storage].cells.len() as i64))
            }
            MemoryExpr::Read { resource, index }
            | MemoryExpr::Write {
                resource, index, ..
            } => {
                let r = self.access(resources, *resource)?;
                let Value::Integer(index) = self.expr(index, env, resources, function, depth)?
                else {
                    return Err(EvalError::InvalidIr);
                };
                if index < 0 || index as u64 >= self.buffers[r.storage].cells.len() as u64 {
                    return Err(trap(Trap::IndexOutOfBounds));
                }
                let index = index as usize;
                if let MemoryExpr::Write { value, .. } = memory {
                    if !r.mode.writable() {
                        return Err(EvalError::InvalidIr);
                    }
                    let Value::Integer(value) =
                        self.expr(value, env, resources, function, depth)?
                    else {
                        return Err(EvalError::InvalidIr);
                    };
                    self.buffers[r.storage].cells[index] = value;
                    Ok(Value::Unit)
                } else {
                    Ok(Value::Integer(self.buffers[r.storage].cells[index]))
                }
            }
            MemoryExpr::CallView {
                function: callee,
                resource,
                mode,
                arguments,
            } => {
                let r = self.access(resources, *resource)?;
                self.call(
                    Call {
                        function: *callee,
                        arguments,
                        view: Some((r, *mode)),
                    },
                    env,
                    resources,
                    function,
                    depth,
                    span,
                )
            }
        }
    }
    fn expr(
        &mut self,
        expr: &Expr,
        env: &mut Vec<Value>,
        resources: &mut Vec<Resource>,
        function_id: usize,
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
            ExprKind::Memory(memory) => {
                self.memory_expr(memory, env, resources, function_id, next, expr.span)?
            }
            ExprKind::Tuple(fields) => {
                let mut values = [ScalarValue::Unit; MAX_TUPLE_FIELDS];
                for (i, field) in fields.iter().enumerate() {
                    values[i] = match self.expr(field, env, resources, function_id, next)? {
                        Value::Integer(n) => ScalarValue::Integer(n),
                        Value::Boolean(b) => ScalarValue::Boolean(b),
                        Value::Unit => ScalarValue::Unit,
                        Value::Tuple(_) => return Err(EvalError::InvalidIr),
                    };
                }
                self.construct(&values[..fields.len()], expr.span)?
            }
            ExprKind::Project { value, index } => {
                let Value::Tuple(tuple) = self.expr(value, env, resources, function_id, next)?
                else {
                    return Err(EvalError::InvalidIr);
                };
                tuple
                    .fields()
                    .get(*index)
                    .ok_or(EvalError::InvalidIr)?
                    .as_value()
            }
            ExprKind::Integer(n) => Value::Integer(*n),
            ExprKind::Boolean(b) => Value::Boolean(*b),
            ExprKind::Unit => Value::Unit,
            ExprKind::Local(index) => env
                .get(
                    env.len()
                        .checked_sub(index.checked_add(1).ok_or(EvalError::InvalidIr)?)
                        .ok_or(EvalError::InvalidIr)?,
                )
                .ok_or(EvalError::InvalidIr)?
                .clone(),
            ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                let value = self.expr(value, env, resources, function_id, next)?;
                self.reserve_slots(1, expr.span)?;
                env.push(value);
                let result = self.expr(body, env, resources, function_id, next);
                env.pop();
                self.release_slots(1);
                result?
            }
            ExprKind::Assign { index, value } => {
                let value = self.expr(value, env, resources, function_id, next)?;
                let position = env
                    .len()
                    .checked_sub(index.checked_add(1).ok_or(EvalError::InvalidIr)?)
                    .ok_or(EvalError::InvalidIr)?;
                let target = env.get_mut(position).ok_or(EvalError::InvalidIr)?;
                if !target.same_type(&value) {
                    return Err(EvalError::InvalidIr);
                }
                *target = value;
                Value::Unit
            }
            ExprKind::While { condition, body } => {
                loop {
                    match self.expr(condition, env, resources, function_id, next)? {
                        Value::Boolean(false) => break,
                        Value::Boolean(true) => {
                            if self.expr(body, env, resources, function_id, next)? != Value::Unit {
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
                let Value::Boolean(condition) =
                    self.expr(condition, env, resources, function_id, next)?
                else {
                    return Err(EvalError::InvalidIr);
                };
                self.expr(
                    if condition { then_branch } else { else_branch },
                    env,
                    resources,
                    function_id,
                    next,
                )?
            }
            ExprKind::Unary { op, operand } => {
                let value = self.expr(operand, env, resources, function_id, next)?;
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
                let left = self.expr(left, env, resources, function_id, next)?;
                if *op == BinaryOp::And && left == Value::Boolean(false) {
                    Value::Boolean(false)
                } else if *op == BinaryOp::Or && left == Value::Boolean(true) {
                    Value::Boolean(true)
                } else {
                    let right = self.expr(right, env, resources, function_id, next)?;
                    binary(*op, left, right, expr.span)?
                }
            }
            ExprKind::Call {
                function,
                arguments,
            } => self.call(
                Call {
                    function: *function,
                    arguments,
                    view: None,
                },
                env,
                resources,
                function_id,
                next,
                expr.span,
            )?,
        };
        if !value.has_type(&expr.ty) {
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
        (BinaryOp::Eq, a, b) if a.same_type(&b) => Ok(Value::Boolean(a == b)),
        (BinaryOp::Ne, a, b) if a.same_type(&b) => Ok(Value::Boolean(a != b)),
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

#[cfg(test)]
mod product_budget_tests {
    use super::*;

    #[test]
    fn scalar_and_tuple_type_checks_preserve_exact_shape_validation() {
        let tuple = |fields: &[ScalarValue]| Value::Tuple(TupleValue::new(fields).unwrap());
        let values = [
            Value::Integer(i64::MIN),
            Value::Integer(i64::MAX),
            Value::Boolean(false),
            Value::Boolean(true),
            Value::Unit,
            tuple(&[ScalarValue::Integer(1)]),
            tuple(&[ScalarValue::Integer(2)]),
            tuple(&[ScalarValue::Boolean(true)]),
            tuple(&[ScalarValue::Unit]),
            tuple(&[ScalarValue::Integer(1), ScalarValue::Boolean(false)]),
            tuple(&[ScalarValue::Boolean(false), ScalarValue::Integer(1)]),
            tuple(&[ScalarValue::Integer(1), ScalarValue::Boolean(true)]),
            tuple(&[ScalarValue::Unit; MAX_TUPLE_FIELDS]),
        ];
        for value in &values {
            for other in &values {
                let equal_types = value.ty() == other.ty();
                assert_eq!(value.has_type(&other.ty()), equal_types);
                assert_eq!(value.same_type(other), equal_types);
                for (op, expected) in [
                    (BinaryOp::Eq, value == other),
                    (BinaryOp::Ne, value != other),
                ] {
                    let result = binary(op, value.clone(), other.clone(), Span::default());
                    assert_eq!(
                        result,
                        if equal_types {
                            Ok(Value::Boolean(expected))
                        } else {
                            Err(EvalError::InvalidIr)
                        }
                    );
                }
            }
        }
        for width in 1..=MAX_TUPLE_FIELDS {
            let fields: Vec<_> = (0..width)
                .map(|i| match i % 3 {
                    0 => ScalarValue::Integer(i as i64),
                    1 => ScalarValue::Boolean(true),
                    _ => ScalarValue::Unit,
                })
                .collect();
            let tuple = TupleValue::new(&fields).unwrap();
            assert_eq!(tuple.fields(), fields);
            assert_eq!(
                tuple.shape().fields(),
                fields.iter().map(|v| v.ty()).collect::<Vec<_>>()
            );
            assert_eq!(tuple.clone(), tuple);
            let value = Value::Tuple(tuple.clone());
            assert!(value.has_type(&value.ty()));
            assert!(value.same_type(&value.clone()));
            for other_width in 1..=MAX_TUPLE_FIELDS {
                if other_width != width {
                    let other = Value::Tuple(
                        TupleValue::new(&vec![ScalarValue::Unit; other_width]).unwrap(),
                    );
                    assert!(!value.has_type(&other.ty()));
                    assert!(!value.same_type(&other));
                }
            }
            for field in 0..width {
                let mut changed = fields.clone();
                changed[field] = match changed[field] {
                    ScalarValue::Integer(_) => ScalarValue::Boolean(false),
                    ScalarValue::Boolean(_) => ScalarValue::Unit,
                    ScalarValue::Unit => ScalarValue::Integer(0),
                };
                let other = Value::Tuple(TupleValue::new(&changed).unwrap());
                assert!(!value.has_type(&other.ty()));
                assert!(!value.same_type(&other));
            }
            assert_eq!(
                format!("{tuple:?}"),
                format!("TupleValue {{ fields: {fields:?} }}")
            );
        }
    }

    fn evaluator(program: &Program) -> Evaluator<'_> {
        Evaluator {
            memory: false,
            buffers: Vec::new(),
            live_cells: 0,
            #[cfg(feature = "memory-evidence")]
            evidence: None,
            program,
            fuel: 10000,
            products: program.has_flat_products(),
            tuple_fields: 0,
            active_slots: 0,
        }
    }
    #[test]
    fn tuple_charge_is_checked_before_payload_allocation_and_not_refunded() {
        let p = crate::compile("fn main()->i64{(1,2).0}").unwrap();
        for remaining in [1, 2, 3] {
            let mut e = evaluator(&p);
            e.tuple_fields = MAX_TUPLE_ALLOCATION_FIELDS - remaining;
            let value = e.expr(&p.functions[0].body, &mut Vec::new(), &mut Vec::new(), 0, 0);
            if remaining < 2 {
                assert!(matches!(value, Err(EvalError::ResourceLimit { .. })));
                assert_eq!(e.tuple_fields, MAX_TUPLE_ALLOCATION_FIELDS - remaining);
            } else {
                assert_eq!(value, Ok(Value::Integer(1)));
                assert_eq!(e.tuple_fields, MAX_TUPLE_ALLOCATION_FIELDS - remaining + 2);
            }
        }
        let p = crate::compile("fn main()->i64{(1/0,2).0}").unwrap();
        let mut e = evaluator(&p);
        e.tuple_fields = MAX_TUPLE_ALLOCATION_FIELDS;
        assert!(matches!(
            e.expr(&p.functions[0].body, &mut Vec::new(), &mut Vec::new(), 0, 0),
            Err(EvalError::Trap {
                kind: Trap::DivisionByZero,
                ..
            })
        ));
        assert_eq!(e.tuple_fields, MAX_TUPLE_ALLOCATION_FIELDS);
    }
    #[test]
    fn retained_callers_and_full_unfilled_argument_buffers_are_reserved() {
        let p =
            crate::compile("fn take(x:i64,y:i64)->i64{x+y} fn main()->i64{let p=(1,);take(1/0,2)}")
                .unwrap();
        let mut e = evaluator(&p);
        e.active_slots = MAX_ACTIVE_SLOTS - 2;
        assert!(
            matches!(e.expr(&p.functions[1].body, &mut Vec::new(), &mut Vec::new(), 1, 0),Err(EvalError::ResourceLimit{reason,..}) if reason.contains("slot")),
            "reserve two call slots while retaining the let slot before first trapping argument"
        );
        let p=crate::compile("fn one(x:i64)->i64{x} fn take(x:i64,y:i64)->i64{x+y} fn main()->i64{let p=(1,);take(one(2),3)}").unwrap();
        let mut e = evaluator(&p);
        e.active_slots = MAX_ACTIVE_SLOTS - 3;
        assert!(
            matches!(
                e.expr(&p.functions[2].body, &mut Vec::new(), &mut Vec::new(), 2, 0),
                Err(EvalError::ResourceLimit { .. })
            ),
            "nested argument call retains the outer full reservation"
        );
    }
    #[test]
    fn scopes_calls_and_replacement_release_logical_slots_and_payloads() {
        let p=crate::compile("fn take(p:(i64,))->i64{let q=p;q.0} fn main()->i64{let mut n=0;while(n<100){let p=(n,);take(p);n=n+1;}n}").unwrap();
        let mut e = evaluator(&p);
        e.active_slots = MAX_ACTIVE_SLOTS - 7;
        let seeded = e.active_slots;
        assert_eq!(
            e.expr(&p.functions[1].body, &mut Vec::new(), &mut Vec::new(), 1, 0),
            Ok(Value::Integer(100))
        );
        assert_eq!(e.active_slots, seeded);
        assert_eq!(e.tuple_fields, 100);
        let tuple = TupleValue::new(&[ScalarValue::Integer(42)]).unwrap();
        let weak = Arc::downgrade(&tuple.fields);
        let copy = tuple.clone();
        drop(tuple);
        assert!(weak.upgrade().is_some());
        drop(copy);
        assert!(weak.upgrade().is_none());
        let scalar = crate::compile("fn main()->i64{let x=42;x}").unwrap();
        let mut e = evaluator(&scalar);
        e.active_slots = MAX_ACTIVE_SLOTS;
        assert_eq!(
            e.expr(
                &scalar.functions[0].body,
                &mut Vec::new(),
                &mut Vec::new(),
                0,
                0
            ),
            Ok(Value::Integer(42))
        );
        assert_eq!(e.active_slots, MAX_ACTIVE_SLOTS);
    }
}
