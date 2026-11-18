use super::{CheckedProgram, TailEdge};
pub use crate::mir::origin::{BlockChild, BlockEdge, CoreEdge, MirPath, Origin};
use crate::{
    bounded::{Buffer, OutputError},
    core::{self, ImportError, StrictValue},
    mir::{self, Block, Operation, Signature},
    types::{BinaryOp, Expr, ExprKind, IrRevision},
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, HashSet},
    io::Write,
};

pub const MIR_SCHEMA: &str = "anl-boot-mir-v1";
const MAX_MIR_BYTES: usize = 8_388_608;

/// Checked Core plus its exact canonical MIR. It has no hosted-program conversion.
pub struct CheckedPair {
    pub(super) program: CheckedProgram,
    pub(super) functions: Vec<mir::Function>,
    origins: Vec<Origin>,
    parks: [Origin; 3],
}
impl CheckedPair {
    /// Derived structural locations, not execution or hardware-delivery evidence.
    pub fn origins(&self) -> &[Origin] {
        &self.origins
    }
    /// Boot, hardware and language selected tails, in that order.
    pub fn parks(&self) -> &[Origin; 3] {
        &self.parks
    }
}
#[derive(Debug)]
pub enum PairError {
    Input(ImportError),
    Invariant(OutputError),
}
impl std::fmt::Display for PairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Input(e) => e.fmt(f),
            Self::Invariant(e) => e.fmt(f),
        }
    }
}
impl std::error::Error for PairError {}
impl From<ImportError> for PairError {
    fn from(e: ImportError) -> Self {
        Self::Input(e)
    }
}
fn bad(s: impl Into<String>) -> ImportError {
    ImportError::Invalid(s.into())
}
fn invariant(s: impl Into<String>) -> OutputError {
    OutputError::Infrastructure(s.into())
}
fn signatures(program: &CheckedProgram) -> Vec<Signature> {
    program
        .functions
        .iter()
        .map(|f| Signature {
            view: None,
            params: f.params.clone(),
            result: f.result,
        })
        .chain(program.primitives.iter().map(|p| Signature {
            view: None,
            params: p.params.clone(),
            result: p.result,
        }))
        .collect()
}
pub(super) fn core_at<'a>(mut expr: &'a Expr, path: &[CoreEdge]) -> Option<&'a Expr> {
    for edge in path {
        expr = match (edge, &expr.kind) {
            (CoreEdge::LetValue, ExprKind::Let { value, .. } | ExprKind::LetMut { value, .. }) => {
                value
            }
            (CoreEdge::LetBody, ExprKind::Let { body, .. } | ExprKind::LetMut { body, .. }) => body,
            (CoreEdge::WhileCondition, ExprKind::While { condition, .. }) => condition,
            (CoreEdge::WhileBody, ExprKind::While { body, .. }) => body,
            (CoreEdge::IfCondition, ExprKind::If { condition, .. }) => condition,
            (CoreEdge::IfThen, ExprKind::If { then_branch, .. }) => then_branch,
            (CoreEdge::IfElse, ExprKind::If { else_branch, .. }) => else_branch,
            (CoreEdge::UnaryOperand, ExprKind::Unary { operand, .. }) => operand,
            (CoreEdge::BinaryLeft, ExprKind::Binary { left, .. }) => left,
            (CoreEdge::BinaryRight, ExprKind::Binary { right, .. }) => right,
            (CoreEdge::CallArgument(i), ExprKind::Call { arguments, .. }) => arguments.get(*i)?,
            (CoreEdge::ConvertOperand, ExprKind::Convert { operand, .. }) => operand,
            (CoreEdge::TupleField(i), ExprKind::Tuple(fields)) => fields.get(*i)?,
            (CoreEdge::ProjectOperand, ExprKind::Project { value, .. }) => value,
            (CoreEdge::AssignValue, ExprKind::Assign { value, .. }) => value,
            _ => return None,
        };
    }
    Some(expr)
}
fn operation_agrees(expr: &Expr, operation: &Operation) -> bool {
    match (&expr.kind, operation) {
        (ExprKind::Word(a), Operation::Word(b)) => a == b,
        (
            ExprKind::Convert {
                mode: a, target: x, ..
            },
            Operation::Convert {
                mode: b, target: y, ..
            },
        ) => a == b && x == y,
        (ExprKind::Tuple(a), Operation::Tuple(b)) => a.len() == b.len(),
        (ExprKind::Project { index: a, .. }, Operation::Project(_, b)) => a == b,
        (ExprKind::Integer(a), Operation::Integer(b)) => a == b,
        (ExprKind::Boolean(a), Operation::Boolean(b)) => a == b,
        (ExprKind::Unit, Operation::Unit)
        | (ExprKind::Local(_), Operation::Load(_))
        | (ExprKind::LetMut { .. }, Operation::MutableScope { .. })
        | (ExprKind::Assign { .. }, Operation::Store(..))
        | (ExprKind::While { .. }, Operation::While { .. })
        | (ExprKind::If { .. }, Operation::Branch { .. }) => true,
        (ExprKind::Unary { op: a, .. }, Operation::Unary(b, _)) => a == b,
        (ExprKind::Binary { op: a, .. }, Operation::Binary(b, _, _)) => a == b,
        (
            ExprKind::Binary {
                op: BinaryOp::And | BinaryOp::Or,
                ..
            },
            Operation::Branch { .. },
        ) => true,
        (
            ExprKind::Call {
                function: a,
                arguments: x,
            },
            Operation::Call(b, y),
        ) => a == b && x.len() == y.len(),
        _ => false,
    }
}
fn locations(
    function: usize,
    core: &Expr,
    block: &Block,
    joins: mir::EmissionOrigins,
) -> Result<Vec<Origin>, OutputError> {
    let mut table = BTreeMap::new();
    let mut occurrences = HashSet::new();
    for (temp, path) in joins {
        if !occurrences.insert(path.clone()) {
            return Err(invariant("duplicate emitting Core occurrence"));
        }
        if table.insert(temp.id, (temp.ty, path)).is_some() {
            return Err(invariant("duplicate emitting temporary"));
        }
    }
    fn walk(
        function: usize,
        core: &Expr,
        block: &Block,
        path: &mut Vec<BlockEdge>,
        table: &mut BTreeMap<usize, (crate::types::Type, Vec<CoreEdge>)>,
        output: &mut Vec<Origin>,
    ) -> Result<(), OutputError> {
        for (index, instruction) in block.instructions.iter().enumerate() {
            let (ty, core_path) = table
                .remove(&instruction.destination.id)
                .ok_or_else(|| invariant("missing emitting Core occurrence"))?;
            let source =
                core_at(core, &core_path).ok_or_else(|| invariant("unresolved Core occurrence"))?;
            if ty != instruction.destination.ty
                || source.ty != ty
                || !operation_agrees(source, &instruction.kind)
            {
                return Err(invariant(
                    "emitting occurrence disagrees with MIR operation",
                ));
            }
            output.push(Origin {
                function,
                core_path,
                mir_path: MirPath {
                    blocks: path.clone(),
                    instruction: index,
                },
            });
            let children: Vec<_> = match &instruction.kind {
                Operation::MutableScope { body, .. } => vec![(BlockChild::MutableBody, body)],
                Operation::While { condition, body } => vec![
                    (BlockChild::WhileCondition, condition),
                    (BlockChild::WhileBody, body),
                ],
                Operation::Branch {
                    then_block,
                    else_block,
                    ..
                } => vec![
                    (BlockChild::BranchThen, then_block),
                    (BlockChild::BranchElse, else_block),
                ],
                Operation::Memory(_) => return Err(invariant("boot origin map contains memory")),
                _ => vec![],
            };
            for (child, block) in children {
                path.push(BlockEdge {
                    instruction: index,
                    child,
                });
                walk(function, core, block, path, table, output)?;
                path.pop();
            }
        }
        Ok(())
    }
    let mut output = Vec::new();
    walk(
        function,
        core,
        block,
        &mut Vec::new(),
        &mut table,
        &mut output,
    )?;
    if !table.is_empty() {
        return Err(invariant("emitting temporary has no MIR declaration"));
    }
    Ok(output)
}
pub(super) fn mir_at<'a>(mut block: &'a Block, path: &MirPath) -> Option<&'a mir::Instruction> {
    for edge in &path.blocks {
        block = match (&block.instructions.get(edge.instruction)?.kind, edge.child) {
            (Operation::MutableScope { body, .. }, BlockChild::MutableBody) => body,
            (Operation::While { condition, .. }, BlockChild::WhileCondition) => condition,
            (Operation::While { body, .. }, BlockChild::WhileBody) => body,
            (Operation::Branch { then_block, .. }, BlockChild::BranchThen) => then_block,
            (Operation::Branch { else_block, .. }, BlockChild::BranchElse) => else_block,
            _ => return None,
        }
    }
    block.instructions.get(path.instruction)
}
fn park_block(block: &Block, boolean: bool) -> bool {
    let [instruction] = block.instructions.as_slice() else {
        return false;
    };
    instruction.destination == block.yield_value
        && if boolean {
            matches!(instruction.kind, Operation::Boolean(true))
        } else {
            matches!(instruction.kind, Operation::Unit)
        }
}
pub fn lower(program: CheckedProgram) -> Result<CheckedPair, OutputError> {
    let mut functions = Vec::new();
    let mut origins = Vec::new();
    for (id, function) in program.functions.iter().enumerate() {
        let (lowered, joins) =
            mir::lower_function(function, true).map_err(|e| invariant(e.to_string()))?;
        origins.extend(locations(id, &function.body, &lowered.body, joins)?);
        functions.push(lowered);
    }
    mir::validate_functions(
        &functions,
        &signatures(&program),
        IrRevision::WordsV4,
        false,
    )
    .map_err(|e| invariant(e.to_string()))?;
    let mut parks = Vec::new();
    for (role, function) in program.entries.iter().copied().enumerate() {
        let path: Vec<_> = program._tails[role]
            .iter()
            .map(|e| match e {
                TailEdge::Value => CoreEdge::LetValue,
                TailEdge::Body => CoreEdge::LetBody,
            })
            .collect();
        let mut candidates = origins
            .iter()
            .filter(|o| o.function == function && o.core_path == path);
        let selected = candidates
            .next()
            .ok_or_else(|| invariant("selected tail has no emitting origin"))?;
        if candidates.next().is_some() {
            return Err(invariant("selected tail has multiple emitting origins"));
        }
        let source = core_at(&program.functions[function].body, &path)
            .ok_or_else(|| invariant("selected Core tail unresolved"))?;
        let ExprKind::While { condition, body } = &source.kind else {
            return Err(invariant("selected Core tail is not while"));
        };
        if !matches!(condition.kind, ExprKind::Boolean(true))
            || !matches!(body.kind, ExprKind::Unit)
        {
            return Err(invariant("selected Core tail is not park"));
        }
        let actual = mir_at(&functions[function].body, &selected.mir_path)
            .ok_or_else(|| invariant("selected MIR tail unresolved"))?;
        let Operation::While { condition, body } = &actual.kind else {
            return Err(invariant("selected MIR tail is not while"));
        };
        if !park_block(condition, true) || !park_block(body, false) {
            return Err(invariant("selected MIR tail is not canonical park"));
        }
        parks.push(selected.clone());
    }
    Ok(CheckedPair {
        program,
        functions,
        origins,
        parks: parks
            .try_into()
            .map_err(|_| invariant("missing selected role"))?,
    })
}
fn value(pair: &CheckedPair) -> Value {
    let mut value = super::wire::metadata(pair.program.entries);
    value["schema"] = json!(MIR_SCHEMA);
    let mut rows = Vec::new();
    for (id, function) in pair.functions.iter().enumerate() {
        rows.push(json!({"kind":"defined", "id":id, "name":pair.program.functions[id].name, "view":null, "params":function.params, "result":function.result, "effects":pair.program.effects[id], "body":function.body, "temp_count":function.temp_count, "slot_count":function.slot_count, "resource_count":0}));
    }
    for p in &pair.program.primitives {
        rows.push(json!({"kind":"primitive", "id":p.id, "name":p.name, "operation":super::wire::operation_value(&p.operation), "params":p.params, "result":p.result, "effects":p.effects}));
    }
    value["functions"] = Value::Array(rows);
    value
}
pub fn export_pair_core(pair: &CheckedPair) -> Result<String, OutputError> {
    super::export_core(&pair.program)
}
pub fn export_mir(pair: &CheckedPair) -> Result<String, OutputError> {
    let mut buffer = Buffer::new(Some(MAX_MIR_BYTES), "boot MIR output exceeds 8388608 bytes");
    let result = serde_json::to_writer(&mut buffer, &value(pair));
    if result.is_ok() {
        let _ = buffer.write_all(b"\n");
    }
    let text = buffer.finish()?;
    result.map_err(|e| invariant(e.to_string()))?;
    Ok(text)
}
pub fn import_pair(core_text: &str, mir_text: &str) -> Result<CheckedPair, PairError> {
    let program = super::import_core(core_text)?;
    if mir_text.len() > MAX_MIR_BYTES {
        return Err(ImportError::ResourceLimit("boot MIR exceeds 8388608 bytes".into()).into());
    }
    super::wire::numeric_tokens(mir_text)?;
    let StrictValue(document) = serde_json::from_str(mir_text).map_err(|e| {
        let message = e.to_string();
        if e.is_syntax() && message.starts_with("recursion limit exceeded at line ") {
            ImportError::ResourceLimit(message)
        } else {
            bad(message)
        }
    })?;
    let root = core::object(
        &document,
        &[
            "schema",
            "semantic_revision",
            "ordinary_semantic_revision",
            "target_profile",
            "image",
            "stacks",
            "devices",
            "entries",
            "functions",
        ],
    )?;
    let pair = lower(program).map_err(PairError::Invariant)?;
    let expected = value(&pair);
    for (key, value) in expected.as_object().expect("boot MIR envelope") {
        if key != "functions" && &root[key] != value {
            return Err(bad(format!("boot MIR {key} differs from checked Core")).into());
        }
    }
    let rows = core::array(&root["functions"])?;
    let expected_rows = expected["functions"].as_array().expect("MIR declarations");
    if rows.len() != expected_rows.len() {
        return Err(bad("MIR declaration count differs from Core").into());
    }
    let mut decoded = Vec::new();
    for (id, row) in rows.iter().enumerate() {
        if id < pair.functions.len() {
            let fields = core::object(
                row,
                &[
                    "kind",
                    "id",
                    "name",
                    "view",
                    "params",
                    "result",
                    "effects",
                    "body",
                    "temp_count",
                    "slot_count",
                    "resource_count",
                ],
            )?;
            for key in ["kind", "id", "name", "view", "result", "effects"] {
                if fields[key] != expected_rows[id][key] {
                    return Err(bad("MIR defined metadata differs from Core").into());
                }
            }
            decoded.push(mir::decode_boot_function(row, rows.len())?);
        } else if row != &expected_rows[id] {
            return Err(bad("MIR primitive declaration differs from Core").into());
        }
    }
    mir::validate_functions(
        &decoded,
        &signatures(&pair.program),
        IrRevision::WordsV4,
        false,
    )
    .map_err(|e| bad(e.to_string()))?;
    if decoded != pair.functions {
        return Err(bad("MIR bodies/counts are not canonical lowering of Core").into());
    }
    Ok(pair)
}
