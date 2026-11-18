mod body_wire;
pub(crate) mod origin;
#[cfg(feature = "memory-evidence")]
pub(crate) mod wire;
use origin::CoreEdge;
// Structured scalar MIR. Blocks sequence instructions and yield one value.
// Checked arithmetic operations include their trap behavior, never raw partial
// arithmetic. Branch-local temporaries cannot escape except through the yield.
use crate::types::{
    self, BinaryOp, Expr, ExprKind, IrRevision, MemoryExpr, ResourceMode, Type, UnaryOp, ViewMode,
};
use crate::word::{ConvertMode, WordValue};
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Temp {
    pub id: usize,
    pub ty: Type,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Slot {
    pub id: usize,
    pub ty: Type,
}

#[derive(Debug)]
pub(crate) struct Program {
    pub revision: IrRevision,
    pub allocation_profile: Option<crate::memory::AllocationProfile>,
    pub functions: Vec<Function>,
    pub entry: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Function {
    pub view: Option<(ViewMode, usize)>,
    pub resource_count: usize,
    pub params: Vec<Temp>,
    pub result: Type,
    pub body: Block,
    pub temp_count: usize,
    pub slot_count: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Block {
    pub instructions: Vec<Instruction>,
    pub yield_value: Temp,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Instruction {
    pub destination: Temp,
    pub kind: Operation,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum MemoryOperation {
    HeapScope {
        site: usize,
        owner: usize,
        length: Temp,
        initial: Block,
        success: Block,
        failure: Block,
    },
    Length {
        resource: usize,
    },
    Read {
        resource: usize,
        index: Temp,
    },
    Write {
        resource: usize,
        index: Temp,
        value: Block,
    },
    CallView {
        function: usize,
        resource: usize,
        mode: ViewMode,
        arguments: Vec<Temp>,
    },
}
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Operation {
    Word(WordValue),
    Convert {
        mode: ConvertMode,
        target: Type,
        operand: Temp,
    },
    Memory(Box<MemoryOperation>),
    Tuple(Vec<Temp>),
    Project(Temp, usize),
    Integer(i64),
    Boolean(bool),
    Unit,
    Unary(UnaryOp, Temp),
    Binary(BinaryOp, Temp, Temp),
    Call(usize, Vec<Temp>),
    MutableScope {
        slot: Slot,
        initial: Temp,
        body: Block,
    },
    Load(Slot),
    Store(Slot, Temp),
    While {
        condition: Block,
        body: Block,
    },
    Branch {
        condition: Temp,
        then_block: Block,
        else_block: Block,
    },
}

impl Program {
    pub fn has_memory(&self) -> bool {
        fn block(b: &Block) -> bool {
            b.instructions.iter().any(|i| match &i.kind {
                Operation::Memory(_) => true,
                Operation::MutableScope { body, .. } => block(body),
                Operation::While { condition, body } => block(condition) || block(body),
                Operation::Branch {
                    then_block,
                    else_block,
                    ..
                } => block(then_block) || block(else_block),
                _ => false,
            })
        }
        self.functions
            .iter()
            .any(|f| f.view.is_some() || block(&f.body))
    }
}

#[derive(Debug)]
pub(crate) struct InvalidMir(&'static str);
impl fmt::Display for InvalidMir {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "native lowering invariant failed: {}", self.0)
    }
}
impl std::error::Error for InvalidMir {}

type Result<T> = std::result::Result<T, InvalidMir>;

pub(crate) fn lower(source: &types::Program, entry: usize) -> Result<Program> {
    let functions = source
        .functions
        .iter()
        .map(|function| lower_function(function, false).map(|(f, _)| f))
        .collect::<Result<Vec<_>>>()?;
    let program = Program {
        revision: source.effective_revision(),
        allocation_profile: source.allocation_profile,
        functions,
        entry,
    };
    validate(&program)?;
    Ok(program)
}

pub(crate) type EmissionOrigins = Vec<(Temp, Vec<CoreEdge>)>;
pub(crate) fn lower_function(
    function: &types::Function,
    record_origins: bool,
) -> Result<(Function, EmissionOrigins)> {
    let mut builder = Builder {
        next: 0,
        next_slot: 0,
        resources: function.view.into_iter().map(|_| 0).collect(),
        view_offset: usize::from(function.view.is_some()),
        resource_count: usize::from(function.view.is_some()),
        origins: record_origins.then(Vec::new),
        path: Vec::new(),
    };
    let params: Vec<_> = function.params.iter().map(|ty| builder.temp(*ty)).collect();
    let mut locals = params.iter().copied().map(Binding::Value).collect();
    let body = builder.block(&function.body, &mut locals)?;
    Ok((
        Function {
            view: function.view.map(|m| (m, 0)),
            resource_count: builder.resource_count,
            params,
            result: function.result,
            body,
            temp_count: builder.next,
            slot_count: builder.next_slot,
        },
        builder.origins.unwrap_or_default(),
    ))
}

#[derive(Clone, Debug)]
pub(crate) struct Signature {
    pub view: Option<ViewMode>,
    pub params: Vec<Type>,
    pub result: Type,
}

#[derive(Clone, Copy)]
enum Binding {
    Value(Temp),
    Mutable(Slot),
}

struct Builder {
    origins: Option<EmissionOrigins>,
    path: Vec<CoreEdge>,
    resources: Vec<usize>,
    view_offset: usize,
    resource_count: usize,
    next: usize,
    next_slot: usize,
}
impl Builder {
    fn child(
        &mut self,
        edge: CoreEdge,
        expr: &Expr,
        locals: &mut Vec<Binding>,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Temp> {
        if self.origins.is_some() {
            self.path.push(edge);
        }
        let result = self.expr(expr, locals, instructions);
        if self.origins.is_some() {
            self.path.pop();
        }
        result
    }
    fn child_block(
        &mut self,
        edge: CoreEdge,
        expr: &Expr,
        locals: &mut Vec<Binding>,
    ) -> Result<Block> {
        if self.origins.is_some() {
            self.path.push(edge);
        }
        let result = self.block(expr, locals);
        if self.origins.is_some() {
            self.path.pop();
        }
        result
    }
    fn resource(&self, index: usize) -> Result<usize> {
        let p = self
            .resources
            .len()
            .checked_sub(
                index
                    .checked_add(1)
                    .ok_or(InvalidMir("resource index overflow"))?,
            )
            .ok_or(InvalidMir("resource out of scope"))?;
        self.resources
            .get(p)
            .copied()
            .ok_or(InvalidMir("resource out of scope"))
    }
    fn memory(
        &mut self,
        memory: &MemoryExpr,
        locals: &mut Vec<Binding>,
        instructions: &mut Vec<Instruction>,
    ) -> Result<MemoryOperation> {
        Ok(match memory {
            MemoryExpr::Heap {
                site,
                length,
                initial,
                success,
                failure,
            } => {
                let owner = site
                    .checked_add(self.view_offset)
                    .ok_or(InvalidMir("resource identity overflow"))?;
                self.resource_count = self.resource_count.max(
                    owner
                        .checked_add(1)
                        .ok_or(InvalidMir("resource count overflow"))?,
                );
                let length = self.expr(length, locals, instructions)?;
                let initial = self.block(initial, locals)?;
                self.resources.push(owner);
                let success = self.block(success, locals);
                self.resources.pop();
                let success = success?;
                let failure = self.block(failure, locals)?;
                MemoryOperation::HeapScope {
                    site: *site,
                    owner,
                    length,
                    initial,
                    success,
                    failure,
                }
            }
            MemoryExpr::Length { resource } => MemoryOperation::Length {
                resource: self.resource(*resource)?,
            },
            MemoryExpr::Read { resource, index } => MemoryOperation::Read {
                resource: self.resource(*resource)?,
                index: self.expr(index, locals, instructions)?,
            },
            MemoryExpr::Write {
                resource,
                index,
                value,
            } => {
                let resource = self.resource(*resource)?;
                let index = self.expr(index, locals, instructions)?;
                let value = self.block(value, locals)?;
                MemoryOperation::Write {
                    resource,
                    index,
                    value,
                }
            }
            MemoryExpr::CallView {
                function,
                resource,
                mode,
                arguments,
            } => {
                let resource = self.resource(*resource)?;
                let mut values = Vec::with_capacity(arguments.len());
                for a in arguments {
                    values.push(self.expr(a, locals, instructions)?);
                }
                MemoryOperation::CallView {
                    function: *function,
                    resource,
                    mode: *mode,
                    arguments: values,
                }
            }
        })
    }
    fn temp(&mut self, ty: Type) -> Temp {
        let temp = Temp { id: self.next, ty };
        self.next += 1;
        temp
    }
    fn block(&mut self, expr: &Expr, locals: &mut Vec<Binding>) -> Result<Block> {
        let mut instructions = Vec::new();
        let yield_value = self.expr(expr, locals, &mut instructions)?;
        Ok(Block {
            instructions,
            yield_value,
        })
    }
    fn expr(
        &mut self,
        expr: &Expr,
        locals: &mut Vec<Binding>,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Temp> {
        let kind = match &expr.kind {
            ExprKind::Word(w) => Operation::Word(*w),
            ExprKind::Convert {
                mode,
                target,
                operand,
            } => Operation::Convert {
                mode: *mode,
                target: *target,
                operand: self.child(CoreEdge::ConvertOperand, operand, locals, instructions)?,
            },
            ExprKind::Memory(memory) => {
                if self.origins.is_some() {
                    return Err(InvalidMir("boot origin lowering forbids memory"));
                }
                Operation::Memory(Box::new(self.memory(memory, locals, instructions)?))
            }
            ExprKind::Tuple(fields) => {
                let mut values = Vec::with_capacity(fields.len());
                for (index, field) in fields.iter().enumerate() {
                    values.push(self.child(
                        CoreEdge::TupleField(index),
                        field,
                        locals,
                        instructions,
                    )?);
                }
                Operation::Tuple(values)
            }
            ExprKind::Project { value, index } => Operation::Project(
                self.child(CoreEdge::ProjectOperand, value, locals, instructions)?,
                *index,
            ),
            ExprKind::Integer(n) => Operation::Integer(*n),
            ExprKind::Boolean(b) => Operation::Boolean(*b),
            ExprKind::Unit => Operation::Unit,
            ExprKind::Local(index) => {
                let index = locals
                    .len()
                    .checked_sub(index.checked_add(1).ok_or(InvalidMir("unbound local"))?)
                    .ok_or(InvalidMir("unbound local"))?;
                match locals
                    .get(index)
                    .copied()
                    .ok_or(InvalidMir("unbound local"))?
                {
                    Binding::Value(temp) => return Ok(temp),
                    Binding::Mutable(slot) => Operation::Load(slot),
                }
            }
            ExprKind::Let { value, body } => {
                let value = self.child(CoreEdge::LetValue, value, locals, instructions)?;
                locals.push(Binding::Value(value));
                let result = self.child(CoreEdge::LetBody, body, locals, instructions);
                locals.pop();
                return result;
            }
            ExprKind::LetMut { value, body } => {
                let initial = self.child(CoreEdge::LetValue, value, locals, instructions)?;
                let slot = Slot {
                    id: self.next_slot,
                    ty: initial.ty,
                };
                self.next_slot += 1;
                locals.push(Binding::Mutable(slot));
                let body = self.child_block(CoreEdge::LetBody, body, locals);
                locals.pop();
                Operation::MutableScope {
                    slot,
                    initial,
                    body: body?,
                }
            }
            ExprKind::Assign { index, value } => {
                let index = locals
                    .len()
                    .checked_sub(
                        index
                            .checked_add(1)
                            .ok_or(InvalidMir("unbound assignment"))?,
                    )
                    .ok_or(InvalidMir("unbound assignment"))?;
                let Binding::Mutable(slot) = locals[index] else {
                    return Err(InvalidMir("assignment target is immutable"));
                };
                let value = self.child(CoreEdge::AssignValue, value, locals, instructions)?;
                Operation::Store(slot, value)
            }
            ExprKind::While { condition, body } => Operation::While {
                condition: self.child_block(CoreEdge::WhileCondition, condition, locals)?,
                body: self.child_block(CoreEdge::WhileBody, body, locals)?,
            },
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition =
                    self.child(CoreEdge::IfCondition, condition, locals, instructions)?;
                let then_block = self.child_block(CoreEdge::IfThen, then_branch, locals)?;
                let else_block = self.child_block(CoreEdge::IfElse, else_branch, locals)?;
                Operation::Branch {
                    condition,
                    then_block,
                    else_block,
                }
            }
            ExprKind::Unary { op, operand } => Operation::Unary(
                *op,
                self.child(CoreEdge::UnaryOperand, operand, locals, instructions)?,
            ),
            ExprKind::Binary { op, left, right } => {
                let left = self.child(CoreEdge::BinaryLeft, left, locals, instructions)?;
                if matches!(op, BinaryOp::And | BinaryOp::Or) {
                    let right_block = self.child_block(CoreEdge::BinaryRight, right, locals)?;
                    let short_block = Block {
                        instructions: Vec::new(),
                        yield_value: left,
                    };
                    let (then_block, else_block) = if *op == BinaryOp::And {
                        (right_block, short_block)
                    } else {
                        (short_block, right_block)
                    };
                    Operation::Branch {
                        condition: left,
                        then_block,
                        else_block,
                    }
                } else {
                    let right = self.child(CoreEdge::BinaryRight, right, locals, instructions)?;
                    Operation::Binary(*op, left, right)
                }
            }
            ExprKind::Call {
                function,
                arguments,
            } => {
                let mut values = Vec::with_capacity(arguments.len());
                for (index, argument) in arguments.iter().enumerate() {
                    values.push(self.child(
                        CoreEdge::CallArgument(index),
                        argument,
                        locals,
                        instructions,
                    )?);
                }
                Operation::Call(*function, values)
            }
        };
        let destination = self.temp(expr.ty);
        if let Some(origins) = &mut self.origins {
            origins.push((destination, self.path.clone()));
        }
        instructions.push(Instruction { destination, kind });
        Ok(destination)
    }
}

fn validate(program: &Program) -> Result<()> {
    let entry = program
        .functions
        .get(program.entry)
        .ok_or(InvalidMir("invalid entry"))?;
    if entry.view.is_some() || !entry.params.is_empty() || entry.result != Type::I64 {
        return Err(InvalidMir("entry must be nullary and return i64"));
    }
    let signatures: Vec<_> = program
        .functions
        .iter()
        .map(|f| Signature {
            view: f.view.map(|(mode, _)| mode),
            params: f.params.iter().map(|p| p.ty).collect(),
            result: f.result,
        })
        .collect();
    validate_functions(&program.functions, &signatures, program.revision, true)
}

pub(crate) fn validate_functions(
    functions: &[Function],
    signatures: &[Signature],
    revision: IrRevision,
    allow_memory: bool,
) -> Result<()> {
    for (id, function) in functions.iter().enumerate() {
        let signature = signatures
            .get(id)
            .ok_or(InvalidMir("missing function signature"))?;
        if function.view.map(|(mode, _)| mode) != signature.view
            || function.params.iter().map(|p| p.ty).collect::<Vec<_>>() != signature.params
            || function.result != signature.result
        {
            return Err(InvalidMir("defined function signature mismatch"));
        }
        if !allow_memory && (function.view.is_some() || function.resource_count != 0) {
            return Err(InvalidMir("boot MIR forbids resources"));
        }

        let mut validator = Validator {
            signatures,
            revision,
            allow_memory,
            resources: vec![None; function.resource_count],
            visible_resources: vec![false; function.resource_count],
            definitions: vec![None; function.temp_count],
            visible: vec![false; function.temp_count],
            slots: vec![None; function.slot_count],
            visible_slots: vec![false; function.slot_count],
        };
        if let Some((mode, id)) = function.view {
            validator.define_resource(id, mode.into())?;
        }
        for param in &function.params {
            validator.define(*param)?;
        }
        if validator.block(&function.body)? != function.result {
            return Err(InvalidMir("function yield type mismatch"));
        }
        if validator.definitions.iter().any(Option::is_none) {
            return Err(InvalidMir("temporary table contains undefined entries"));
        }
        if validator.resources.iter().any(Option::is_none) {
            return Err(InvalidMir("resource table contains undefined entries"));
        }
        if validator.slots.iter().any(Option::is_none) {
            return Err(InvalidMir("slot table contains undefined entries"));
        }
    }
    Ok(())
}

struct Validator<'a> {
    resources: Vec<Option<ResourceMode>>,
    visible_resources: Vec<bool>,
    signatures: &'a [Signature],
    revision: IrRevision,
    allow_memory: bool,
    definitions: Vec<Option<Type>>,
    visible: Vec<bool>,
    slots: Vec<Option<Type>>,
    visible_slots: Vec<bool>,
}
impl Validator<'_> {
    fn define_resource(&mut self, id: usize, mode: ResourceMode) -> Result<()> {
        let slot = self
            .resources
            .get_mut(id)
            .ok_or(InvalidMir("resource out of range"))?;
        if slot.is_some() {
            return Err(InvalidMir("resource defined twice"));
        }
        *slot = Some(mode);
        self.visible_resources[id] = true;
        Ok(())
    }
    fn resource(&self, id: usize) -> Result<ResourceMode> {
        if self.visible_resources.get(id) != Some(&true) {
            return Err(InvalidMir("resource out of scope"));
        }
        self.resources
            .get(id)
            .copied()
            .flatten()
            .ok_or(InvalidMir("undefined resource"))
    }
    fn memory(&mut self, m: &MemoryOperation) -> Result<Type> {
        Ok(match m {
            MemoryOperation::HeapScope {
                owner,
                length,
                initial,
                success,
                failure,
                ..
            } => {
                if self.use_temp(*length)? != Type::I64 || self.block(initial)? != Type::I64 {
                    return Err(InvalidMir("heap operands must be i64"));
                }
                self.define_resource(*owner, ResourceMode::Owner)?;
                let a = self.block(success)?;
                self.visible_resources[*owner] = false;
                let b = self.block(failure)?;
                if a != b {
                    return Err(InvalidMir("heap branch types differ"));
                }
                a
            }
            MemoryOperation::Length { resource } => {
                self.resource(*resource)?;
                Type::I64
            }
            MemoryOperation::Read { resource, index } => {
                self.resource(*resource)?;
                if self.use_temp(*index)? != Type::I64 {
                    return Err(InvalidMir("buffer index must be i64"));
                }
                Type::I64
            }
            MemoryOperation::Write {
                resource,
                index,
                value,
            } => {
                if !self.resource(*resource)?.writable()
                    || self.use_temp(*index)? != Type::I64
                    || self.block(value)? != Type::I64
                {
                    return Err(InvalidMir("invalid buffer write"));
                }
                Type::Unit
            }
            MemoryOperation::CallView {
                function,
                resource,
                mode,
                arguments,
            } => {
                if !self.resource(*resource)?.lends(*mode) {
                    return Err(InvalidMir("view permission escalation"));
                }
                let f = self
                    .signatures
                    .get(*function)
                    .ok_or(InvalidMir("invalid view callee"))?;
                if f.view != Some(*mode) || f.params.len() != arguments.len() {
                    return Err(InvalidMir("view call signature mismatch"));
                }
                for (a, p) in arguments.iter().zip(&f.params) {
                    if self.use_temp(*a)? != *p {
                        return Err(InvalidMir("view argument type mismatch"));
                    }
                }
                f.result
            }
        })
    }
    fn define(&mut self, temp: Temp) -> Result<()> {
        let slot = self
            .definitions
            .get_mut(temp.id)
            .ok_or(InvalidMir("temporary out of range"))?;
        if slot.is_some() {
            return Err(InvalidMir("temporary defined twice"));
        }
        *slot = Some(temp.ty);
        self.visible[temp.id] = true;
        Ok(())
    }
    fn use_temp(&self, temp: Temp) -> Result<Type> {
        if self.definitions.get(temp.id) != Some(&Some(temp.ty))
            || self.visible.get(temp.id) != Some(&true)
        {
            return Err(InvalidMir(
                "temporary use is undefined, out of scope, or mistyped",
            ));
        }
        Ok(temp.ty)
    }
    fn use_slot(&self, slot: Slot) -> Result<Type> {
        if self.slots.get(slot.id) != Some(&Some(slot.ty))
            || self.visible_slots.get(slot.id) != Some(&true)
        {
            return Err(InvalidMir(
                "slot use is undefined, out of scope, or mistyped",
            ));
        }
        Ok(slot.ty)
    }
    fn block(&mut self, block: &Block) -> Result<Type> {
        for instruction in &block.instructions {
            let ty = match &instruction.kind {
                Operation::Word(w) => {
                    if self.revision != IrRevision::WordsV4 {
                        return Err(InvalidMir("word operation requires v4"));
                    }
                    Type::Word(w.width())
                }
                Operation::Convert {
                    mode,
                    target,
                    operand,
                } => {
                    if self.revision != IrRevision::WordsV4 {
                        return Err(InvalidMir("conversion requires v4"));
                    }
                    mode.result(self.use_temp(*operand)?, *target)
                        .ok_or(InvalidMir("conversion operand type mismatch"))?
                }
                Operation::Memory(m) => {
                    if !self.allow_memory {
                        return Err(InvalidMir("boot MIR forbids memory"));
                    }
                    self.memory(m)?
                }
                Operation::Tuple(fields) => {
                    if !(1..=types::MAX_TUPLE_FIELDS).contains(&fields.len()) {
                        return Err(InvalidMir("tuple width"));
                    }
                    let mut shape = Vec::new();
                    for field in fields {
                        shape.push(
                            self.use_temp(*field)?
                                .scalar()
                                .ok_or(InvalidMir("nested tuple"))?,
                        );
                    }
                    Type::Tuple(
                        types::TupleShape::new(&shape).map_err(|_| InvalidMir("tuple width"))?,
                    )
                }
                Operation::Project(value, index) => {
                    let Type::Tuple(shape) = self.use_temp(*value)? else {
                        return Err(InvalidMir("projection of scalar"));
                    };
                    shape
                        .fields()
                        .get(*index)
                        .ok_or(InvalidMir("projection out of bounds"))?
                        .as_type()
                }
                Operation::Integer(_) => Type::I64,
                Operation::Boolean(_) => Type::Bool,
                Operation::Unit => Type::Unit,
                Operation::Unary(op, input) => {
                    if op.is_word() && self.revision != IrRevision::WordsV4 {
                        return Err(InvalidMir("word operator requires v4"));
                    }
                    op.result(self.use_temp(*input)?)
                        .ok_or(InvalidMir("unary operand type mismatch"))?
                }
                Operation::Binary(op, left, right) => {
                    if op.is_word() && self.revision != IrRevision::WordsV4 {
                        return Err(InvalidMir("word operator requires v4"));
                    }
                    if matches!(op, BinaryOp::And | BinaryOp::Or) {
                        return Err(InvalidMir("short-circuit operator was not lowered"));
                    }
                    op.result(self.use_temp(*left)?, self.use_temp(*right)?)
                        .ok_or(InvalidMir("binary operand type mismatch"))?
                }
                Operation::Call(id, args) => {
                    let function = self
                        .signatures
                        .get(*id)
                        .ok_or(InvalidMir("invalid callee"))?;
                    if function.view.is_some() || args.len() != function.params.len() {
                        return Err(InvalidMir("call arity mismatch"));
                    }
                    for (arg, param) in args.iter().zip(&function.params) {
                        if self.use_temp(*arg)? != *param {
                            return Err(InvalidMir("call argument type mismatch"));
                        }
                    }
                    function.result
                }
                Operation::MutableScope {
                    slot,
                    initial,
                    body,
                } => {
                    if self.use_temp(*initial)? != slot.ty {
                        return Err(InvalidMir("slot initializer type mismatch"));
                    }
                    let definition = self
                        .slots
                        .get_mut(slot.id)
                        .ok_or(InvalidMir("slot out of range"))?;
                    if definition.is_some() {
                        return Err(InvalidMir("slot defined twice"));
                    }
                    *definition = Some(slot.ty);
                    self.visible_slots[slot.id] = true;
                    let ty = self.block(body)?;
                    self.visible_slots[slot.id] = false;
                    ty
                }
                Operation::Load(slot) => self.use_slot(*slot)?,
                Operation::Store(slot, value) => {
                    if self.use_slot(*slot)? != self.use_temp(*value)? {
                        return Err(InvalidMir("slot store type mismatch"));
                    }
                    Type::Unit
                }
                Operation::While { condition, body } => {
                    if self.block(condition)? != Type::Bool {
                        return Err(InvalidMir("loop condition is not bool"));
                    }
                    if self.block(body)? != Type::Unit {
                        return Err(InvalidMir("loop body is not unit"));
                    }
                    Type::Unit
                }
                Operation::Branch {
                    condition,
                    then_block,
                    else_block,
                } => {
                    if self.use_temp(*condition)? != Type::Bool {
                        return Err(InvalidMir("branch condition is not bool"));
                    }
                    let then_ty = self.block(then_block)?;
                    let else_ty = self.block(else_block)?;
                    if then_ty != else_ty {
                        return Err(InvalidMir("branch yield type mismatch"));
                    }
                    then_ty
                }
            };
            if ty != instruction.destination.ty {
                return Err(InvalidMir("instruction destination type mismatch"));
            }
            self.define(instruction.destination)?;
        }
        let ty = self.use_temp(block.yield_value)?;
        for instruction in &block.instructions {
            self.visible[instruction.destination.id] = false;
        }
        Ok(ty)
    }
}

/// Decode a boot body using actual syntax inventories before allocating validator tables.
pub(crate) fn decode_boot_function(
    row: &serde_json::Value,
    function_count: usize,
) -> std::result::Result<Function, crate::core::ImportError> {
    use crate::core::{self, ImportError};
    use body_wire::{BodyLimits, Counts};
    use serde_json::Value;
    fn bad(s: &str) -> ImportError {
        ImportError::Invalid(s.into())
    }
    fn inventory(
        v: &Value,
        depth: usize,
        counts: &mut Counts,
    ) -> std::result::Result<(), ImportError> {
        if depth >= crate::MAX_DEPTH {
            return Err(ImportError::ResourceLimit(
                "boot MIR block depth exceeded".into(),
            ));
        }
        let b = core::object(v, &["instructions", "yield"])?;
        for i in core::array(&b["instructions"])? {
            let i = core::object(i, &["destination", "operation"])?;
            counts.temps += 1;
            let o = &i["operation"];
            let tag = o
                .get("tag")
                .and_then(Value::as_str)
                .ok_or_else(|| bad("missing MIR operation tag"))?;
            let children: &[&str] = match tag {
                "mutable_scope" => {
                    counts.slots += 1;
                    &["body"]
                }
                "while" => &["condition", "body"],
                "branch" => &["then", "else"],
                "heap_scope" | "buffer_length" | "buffer_read" | "buffer_write" | "call_view" => {
                    return Err(bad("boot MIR forbids memory"));
                }
                _ => &[],
            };
            for child in children {
                inventory(&o[*child], depth + 1, counts)?;
            }
        }
        Ok(())
    }
    let params = core::array(&row["params"])?;
    let mut observed = Counts {
        temps: params.len(),
        ..Counts::default()
    };
    inventory(&row["body"], 0, &mut observed)?;
    for (field, expected) in [
        ("temp_count", observed.temps),
        ("slot_count", observed.slots),
        ("resource_count", 0),
    ] {
        if row[field].as_u64() != Some(expected as u64) {
            return Err(bad("MIR counts do not match actual inventory"));
        }
    }
    if !row["view"].is_null() {
        return Err(bad("boot MIR forbids views"));
    }
    let limits = BodyLimits {
        temps: observed.temps,
        slots: observed.slots,
        functions: function_count,
    };
    let params = body_wire::temps(&row["params"], true, Some(observed.temps))?;
    let mut decoded = Counts {
        temps: params.len(),
        ..Counts::default()
    };
    let body = body_wire::block(&row["body"], 0, &mut decoded, true, Some(limits))?;
    if decoded.temps != observed.temps || decoded.slots != observed.slots || decoded.resources != 0
    {
        return Err(bad("MIR inventory disagreement"));
    }
    Ok(Function {
        view: None,
        resource_count: 0,
        params,
        result: core::ty_words(&row["result"], true, true)?,
        body,
        temp_count: observed.temps,
        slot_count: observed.slots,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn program() -> Program {
        lower(
            &crate::compile("fn main()->i64 { if true { 1 } else { 2 } }").unwrap(),
            0,
        )
        .unwrap()
    }

    #[test]
    fn validator_rejects_uninitialized_and_branch_local_uses() {
        let mut p = program();
        p.functions[0].body.instructions[0].destination.id = 100;
        assert!(validate(&p).is_err());
        let mut p = program();
        let Operation::Branch {
            then_block,
            else_block,
            ..
        } = &mut p.functions[0].body.instructions[1].kind
        else {
            panic!("branch")
        };
        else_block.yield_value = then_block.yield_value;
        assert!(validate(&p).is_err());
    }

    #[test]
    fn validator_rejects_duplicate_definitions_and_wrong_types() {
        let mut p = program();
        p.functions[0].body.instructions[1].destination.id = 0;
        assert!(validate(&p).is_err());
        let mut p = program();
        p.functions[0].body.instructions[0].destination.ty = Type::I64;
        assert!(validate(&p).is_err());
        let mut p = program();
        p.functions[0].result = Type::Bool;
        assert!(validate(&p).is_err());
    }

    #[test]
    fn validator_rejects_invalid_call_and_function_signatures() {
        let source = crate::compile("fn main()->i64 { f(2) } fn f(x:i64)->i64 { x }").unwrap();
        let mut p = lower(&source, 0).unwrap();
        let Operation::Call(_, args) = &mut p.functions[0].body.instructions[1].kind else {
            panic!("call")
        };
        args.clear();
        assert!(validate(&p).is_err());
        let mut p = lower(&source, 0).unwrap();
        p.functions[1].result = Type::Bool;
        assert!(validate(&p).is_err());
        let mut p = lower(&source, 0).unwrap();
        p.functions[1].params[0].ty = Type::Bool;
        assert!(validate(&p).is_err());
        assert!(lower(&source, usize::MAX).is_err());
    }

    fn mutable_program() -> Program {
        lower(
            &crate::compile("fn main()->i64 {let mut x=1;x}").unwrap(),
            0,
        )
        .unwrap()
    }

    #[test]
    fn validator_rejects_uninitialized_escaping_and_mistyped_slots() {
        assert!(validate(&mutable_program()).is_ok());
        let slot = Slot {
            id: 0,
            ty: Type::I64,
        };
        for (before_scope, store) in [(false, false), (true, false), (false, true), (true, true)] {
            let mut p = mutable_program();
            p.functions[0].temp_count += 1;
            let instruction = Instruction {
                destination: Temp {
                    id: 3,
                    ty: if store { Type::Unit } else { Type::I64 },
                },
                kind: if store {
                    Operation::Store(
                        slot,
                        Temp {
                            id: 0,
                            ty: Type::I64,
                        },
                    )
                } else {
                    Operation::Load(slot)
                },
            };
            if before_scope {
                p.functions[0].body.instructions.insert(1, instruction);
            } else {
                p.functions[0].body.instructions.push(instruction);
            }
            assert!(validate(&p).is_err());
        }
        let mut p = mutable_program();
        p.functions[0].body.yield_value = Temp {
            id: 1,
            ty: Type::I64,
        };
        assert!(validate(&p).is_err(), "scope-local temporary escaped");
        for count in [0, 2] {
            let mut p = mutable_program();
            p.functions[0].slot_count = count;
            assert!(validate(&p).is_err());
        }
        let mut p = mutable_program();
        let Operation::MutableScope { slot, .. } = &mut p.functions[0].body.instructions[1].kind
        else {
            panic!("scope")
        };
        slot.ty = Type::Bool;
        assert!(validate(&p).is_err(), "initializer must match slot type");
        let mut p = mutable_program();
        let Operation::MutableScope { body, .. } = &mut p.functions[0].body.instructions[1].kind
        else {
            panic!("scope")
        };
        body.instructions[0].kind = Operation::Load(Slot {
            id: 0,
            ty: Type::Bool,
        });
        assert!(validate(&p).is_err(), "load cannot change slot type");
        let mut p = mutable_program();
        let Operation::MutableScope { body, .. } = &mut p.functions[0].body.instructions[1].kind
        else {
            panic!("scope")
        };
        let boolean = Temp {
            id: 3,
            ty: Type::Bool,
        };
        body.instructions.insert(
            0,
            Instruction {
                destination: boolean,
                kind: Operation::Boolean(true),
            },
        );
        body.instructions[1].kind = Operation::Store(
            Slot {
                id: 0,
                ty: Type::I64,
            },
            boolean,
        );
        p.functions[0].temp_count += 1;
        assert!(validate(&p).is_err(), "store must match slot type");
    }

    #[test]
    fn validator_rejects_duplicate_slot_definitions_across_scopes() {
        let mut p = mutable_program();
        let Operation::MutableScope {
            slot,
            initial,
            body,
        } = &mut p.functions[0].body.instructions[1].kind
        else {
            panic!("scope")
        };
        body.instructions[0].kind = Operation::MutableScope {
            slot: *slot,
            initial: *initial,
            body: Block {
                instructions: vec![],
                yield_value: *initial,
            },
        };
        assert!(validate(&p).is_err());
    }

    #[test]
    fn validator_keeps_loop_blocks_scoped_and_checks_their_yield_types() {
        fn loop_program() -> Program {
            lower(
                &crate::compile("fn main()->i64 {while (false) {} 42}").unwrap(),
                0,
            )
            .unwrap()
        }
        assert!(validate(&loop_program()).is_ok());
        let mut p = loop_program();
        let Operation::While { condition, .. } = &mut p.functions[0].body.instructions[0].kind
        else {
            panic!("loop")
        };
        condition.instructions[0].kind = Operation::Integer(0);
        condition.instructions[0].destination.ty = Type::I64;
        condition.yield_value.ty = Type::I64;
        assert!(validate(&p).is_err(), "condition must yield bool");
        let mut p = loop_program();
        let Operation::While { body, .. } = &mut p.functions[0].body.instructions[0].kind else {
            panic!("loop")
        };
        body.instructions[0].kind = Operation::Boolean(true);
        body.instructions[0].destination.ty = Type::Bool;
        body.yield_value.ty = Type::Bool;
        assert!(validate(&p).is_err(), "body must yield unit");
        let mut p = loop_program();
        let Operation::While { condition, body } = &mut p.functions[0].body.instructions[0].kind
        else {
            panic!("loop")
        };
        body.yield_value = condition.yield_value;
        assert!(
            validate(&p).is_err(),
            "condition temporary leaked into body"
        );
        let mut p = loop_program();
        p.functions[0].body.yield_value = Temp {
            id: 1,
            ty: Type::Unit,
        };
        assert!(validate(&p).is_err(), "body temporary escaped loop");

        let source = crate::compile("fn main()->i64 {while ({let mut x=false;x}) {} 42}").unwrap();
        let mut p = lower(&source, 0).unwrap();
        let loaded = Temp {
            id: p.functions[0].temp_count,
            ty: Type::Bool,
        };
        let Operation::While { body, .. } = &mut p.functions[0].body.instructions[0].kind else {
            panic!("loop")
        };
        body.instructions.push(Instruction {
            destination: loaded,
            kind: Operation::Load(Slot {
                id: 0,
                ty: Type::Bool,
            }),
        });
        p.functions[0].temp_count += 1;
        assert!(validate(&p).is_err(), "condition slot leaked into body");
    }
}
