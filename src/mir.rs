//! Structured scalar MIR. Blocks sequence instructions and yield one value.
//! Checked arithmetic operations include their trap behavior, never raw partial
//! arithmetic. Branch-local temporaries cannot escape except through the yield.
use crate::types::{self, BinaryOp, Expr, ExprKind, Type, UnaryOp};
use std::fmt;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Temp {
    pub id: usize,
    pub ty: Type,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Slot {
    pub id: usize,
    pub ty: Type,
}

#[derive(Debug)]
pub(crate) struct Program {
    pub functions: Vec<Function>,
    pub entry: usize,
}

#[derive(Debug)]
pub(crate) struct Function {
    pub params: Vec<Temp>,
    pub result: Type,
    pub body: Block,
    pub temp_count: usize,
    pub slot_count: usize,
}

#[derive(Debug)]
pub(crate) struct Block {
    pub instructions: Vec<Instruction>,
    pub yield_value: Temp,
}

#[derive(Debug)]
pub(crate) struct Instruction {
    pub destination: Temp,
    pub kind: Operation,
}

#[derive(Debug)]
pub(crate) enum Operation {
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
    let mut functions = Vec::with_capacity(source.functions.len());
    for function in &source.functions {
        let mut builder = Builder {
            next: 0,
            next_slot: 0,
        };
        let params: Vec<_> = function.params.iter().map(|ty| builder.temp(*ty)).collect();
        let mut locals = params.iter().copied().map(Binding::Value).collect();
        let body = builder.block(&function.body, &mut locals)?;
        functions.push(Function {
            params,
            result: function.result,
            body,
            temp_count: builder.next,
            slot_count: builder.next_slot,
        });
    }
    let program = Program { functions, entry };
    validate(&program)?;
    Ok(program)
}

#[derive(Clone, Copy)]
enum Binding {
    Value(Temp),
    Mutable(Slot),
}

struct Builder {
    next: usize,
    next_slot: usize,
}
impl Builder {
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
            ExprKind::Tuple(fields) => {
                let mut values = Vec::with_capacity(fields.len());
                for field in fields {
                    values.push(self.expr(field, locals, instructions)?);
                }
                Operation::Tuple(values)
            }
            ExprKind::Project { value, index } => {
                Operation::Project(self.expr(value, locals, instructions)?, *index)
            }
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
                let value = self.expr(value, locals, instructions)?;
                locals.push(Binding::Value(value));
                let result = self.expr(body, locals, instructions);
                locals.pop();
                return result;
            }
            ExprKind::LetMut { value, body } => {
                let initial = self.expr(value, locals, instructions)?;
                let slot = Slot {
                    id: self.next_slot,
                    ty: initial.ty,
                };
                self.next_slot += 1;
                locals.push(Binding::Mutable(slot));
                let body = self.block(body, locals);
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
                let value = self.expr(value, locals, instructions)?;
                Operation::Store(slot, value)
            }
            ExprKind::While { condition, body } => Operation::While {
                condition: self.block(condition, locals)?,
                body: self.block(body, locals)?,
            },
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.expr(condition, locals, instructions)?;
                let then_block = self.block(then_branch, locals)?;
                let else_block = self.block(else_branch, locals)?;
                Operation::Branch {
                    condition,
                    then_block,
                    else_block,
                }
            }
            ExprKind::Unary { op, operand } => {
                Operation::Unary(*op, self.expr(operand, locals, instructions)?)
            }
            ExprKind::Binary { op, left, right } => {
                let left = self.expr(left, locals, instructions)?;
                if matches!(op, BinaryOp::And | BinaryOp::Or) {
                    let right_block = self.block(right, locals)?;
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
                    let right = self.expr(right, locals, instructions)?;
                    Operation::Binary(*op, left, right)
                }
            }
            ExprKind::Call {
                function,
                arguments,
            } => {
                let mut values = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    values.push(self.expr(argument, locals, instructions)?);
                }
                Operation::Call(*function, values)
            }
        };
        let destination = self.temp(expr.ty);
        instructions.push(Instruction { destination, kind });
        Ok(destination)
    }
}

fn validate(program: &Program) -> Result<()> {
    let entry = program
        .functions
        .get(program.entry)
        .ok_or(InvalidMir("invalid entry"))?;
    if !entry.params.is_empty() || entry.result != Type::I64 {
        return Err(InvalidMir("entry must be nullary and return i64"));
    }
    for function in &program.functions {
        let mut validator = Validator {
            program,
            definitions: vec![None; function.temp_count],
            visible: vec![false; function.temp_count],
            slots: vec![None; function.slot_count],
            visible_slots: vec![false; function.slot_count],
        };
        for param in &function.params {
            validator.define(*param)?;
        }
        if validator.block(&function.body)? != function.result {
            return Err(InvalidMir("function yield type mismatch"));
        }
        if validator.definitions.iter().any(Option::is_none) {
            return Err(InvalidMir("temporary table contains undefined entries"));
        }
        if validator.slots.iter().any(Option::is_none) {
            return Err(InvalidMir("slot table contains undefined entries"));
        }
    }
    Ok(())
}

struct Validator<'a> {
    program: &'a Program,
    definitions: Vec<Option<Type>>,
    visible: Vec<bool>,
    slots: Vec<Option<Type>>,
    visible_slots: Vec<bool>,
}
impl Validator<'_> {
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
                    if self.use_temp(*input)? != op.input() {
                        return Err(InvalidMir("unary operand type mismatch"));
                    }
                    op.input()
                }
                Operation::Binary(op, left, right) => {
                    if matches!(op, BinaryOp::And | BinaryOp::Or) {
                        return Err(InvalidMir("short-circuit operator was not lowered"));
                    }
                    op.result(self.use_temp(*left)?, self.use_temp(*right)?)
                        .ok_or(InvalidMir("binary operand type mismatch"))?
                }
                Operation::Call(id, args) => {
                    let function = self
                        .program
                        .functions
                        .get(*id)
                        .ok_or(InvalidMir("invalid callee"))?;
                    if args.len() != function.params.len() {
                        return Err(InvalidMir("call arity mismatch"));
                    }
                    for (arg, param) in args.iter().zip(&function.params) {
                        if self.use_temp(*arg)? != param.ty {
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
