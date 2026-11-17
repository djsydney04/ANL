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
    Integer(i64),
    Boolean(bool),
    Unit,
    Unary(UnaryOp, Temp),
    Binary(BinaryOp, Temp, Temp),
    Call(usize, Vec<Temp>),
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
        let mut builder = Builder { next: 0 };
        let params: Vec<_> = function.params.iter().map(|ty| builder.temp(*ty)).collect();
        let mut locals = params.clone();
        let body = builder.block(&function.body, &mut locals)?;
        functions.push(Function {
            params,
            result: function.result,
            body,
            temp_count: builder.next,
        });
    }
    let program = Program { functions, entry };
    validate(&program)?;
    Ok(program)
}

struct Builder {
    next: usize,
}
impl Builder {
    fn temp(&mut self, ty: Type) -> Temp {
        let temp = Temp { id: self.next, ty };
        self.next += 1;
        temp
    }
    fn block(&mut self, expr: &Expr, locals: &mut Vec<Temp>) -> Result<Block> {
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
        locals: &mut Vec<Temp>,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Temp> {
        let kind = match &expr.kind {
            ExprKind::Integer(n) => Operation::Integer(*n),
            ExprKind::Boolean(b) => Operation::Boolean(*b),
            ExprKind::Unit => Operation::Unit,
            ExprKind::Local(index) => {
                let index = locals
                    .len()
                    .checked_sub(index.checked_add(1).ok_or(InvalidMir("unbound local"))?)
                    .ok_or(InvalidMir("unbound local"))?;
                return locals
                    .get(index)
                    .copied()
                    .ok_or(InvalidMir("unbound local"));
            }
            ExprKind::Let { value, body } => {
                let value = self.expr(value, locals, instructions)?;
                locals.push(value);
                let result = self.expr(body, locals, instructions);
                locals.pop();
                return result;
            }
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
    }
    Ok(())
}

struct Validator<'a> {
    program: &'a Program,
    definitions: Vec<Option<Type>>,
    visible: Vec<bool>,
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
    fn block(&mut self, block: &Block) -> Result<Type> {
        for instruction in &block.instructions {
            let ty = match &instruction.kind {
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
}
