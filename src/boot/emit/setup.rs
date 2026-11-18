//! Immutable emitter identity for the narrow setup analysis profile.
use super::super::{CheckedPair, Operation, Profile};
use crate::{bounded::OutputError, types::Type};
use std::{fmt, ops::Range};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetupRole {
    Boot,
    Hardware,
    Language,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetupReturn {
    NoReturn,
    UnitByte,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetupOperation {
    ClearSstatusSie,
    WriteSieZero,
    InstallTrap { handler: usize },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetupProfileUnsupported {
    Revision { profile: Profile },
    AdditionalDefinition { function: usize },
    GeneratedHelpers { count: usize },
    NonSetupPrimitive { primitive: usize },
}
impl fmt::Display for SetupProfileUnsupported {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Revision { profile } => {
                write!(out, "setup analysis does not support {}", profile.target())
            }
            Self::AdditionalDefinition { function } => write!(
                out,
                "setup analysis does not support ordinary definition {function}"
            ),
            Self::GeneratedHelpers { count } => write!(
                out,
                "setup analysis does not support {count} generated scalar helpers"
            ),
            Self::NonSetupPrimitive { primitive } => {
                write!(out, "setup analysis does not support primitive {primitive}")
            }
        }
    }
}
impl std::error::Error for SetupProfileUnsupported {}

/// Descriptive row; only the owning emission view supplies its identity.
pub struct SetupFunction {
    id: usize,
    role: SetupRole,
    symbol: String,
    params: Vec<Type>,
    result: Type,
    effects: Vec<u64>,
    c_range: Range<usize>,
}
impl SetupFunction {
    pub fn id(&self) -> usize {
        self.id
    }
    pub fn role(&self) -> SetupRole {
        self.role
    }
    pub fn symbol(&self) -> &str {
        &self.symbol
    }
    pub fn params(&self) -> &[Type] {
        &self.params
    }
    pub fn result(&self) -> Type {
        self.result
    }
    pub fn native_return(&self) -> SetupReturn {
        SetupReturn::NoReturn
    }
    pub fn effects(&self) -> &[u64] {
        &self.effects
    }
    pub fn c_range(&self) -> Range<usize> {
        self.c_range.clone()
    }
}
pub struct SetupPrimitive {
    id: usize,
    operation: SetupOperation,
    symbol: String,
    params: Vec<Type>,
    result: Type,
    effects: Vec<u64>,
    c_range: Range<usize>,
}
impl SetupPrimitive {
    pub fn id(&self) -> usize {
        self.id
    }
    pub fn operation(&self) -> SetupOperation {
        self.operation
    }
    pub fn symbol(&self) -> &str {
        &self.symbol
    }
    pub fn params(&self) -> &[Type] {
        &self.params
    }
    pub fn result(&self) -> Type {
        self.result
    }
    pub fn native_return(&self) -> SetupReturn {
        SetupReturn::UnitByte
    }
    pub fn effects(&self) -> &[u64] {
        &self.effects
    }
    pub fn c_range(&self) -> Range<usize> {
        self.c_range.clone()
    }
}
pub struct SetupAbi {
    role: SetupRole,
    function: usize,
    stack: usize,
    symbol: &'static str,
    assembly_range: Range<usize>,
}
impl SetupAbi {
    pub fn role(&self) -> SetupRole {
        self.role
    }
    pub fn function(&self) -> usize {
        self.function
    }
    pub fn stack(&self) -> usize {
        self.stack
    }
    pub fn symbol(&self) -> &str {
        self.symbol
    }
    pub fn assembly_range(&self) -> Range<usize> {
        self.assembly_range.clone()
    }
}
pub(super) struct SetupIdentity {
    helper_count: usize,
    functions: [SetupFunction; 3],
    primitives: Vec<SetupPrimitive>,
    abi: [SetupAbi; 3],
}
/// Borrowed exact emission facts, never a native code or stack-bound permit.
pub struct SetupEmissionView<'a> {
    files: &'a [(&'static str, String); 6],
    identity: &'a SetupIdentity,
}
impl SetupEmissionView<'_> {
    pub fn functions(&self) -> &[SetupFunction; 3] {
        &self.identity.functions
    }
    pub fn primitives(&self) -> &[SetupPrimitive] {
        &self.identity.primitives
    }
    pub fn abi(&self) -> &[SetupAbi; 3] {
        &self.identity.abi
    }
    pub fn helper_count(&self) -> usize {
        self.identity.helper_count
    }
    pub fn core(&self) -> &str {
        &self.files[0].1
    }
    pub fn mir(&self) -> &str {
        &self.files[1].1
    }
    pub fn c(&self) -> &str {
        &self.files[2].1
    }
    pub fn assembly(&self) -> &str {
        &self.files[3].1
    }
    pub fn linker(&self) -> &str {
        &self.files[4].1
    }
    pub fn manifest(&self) -> &str {
        &self.files[5].1
    }
}
pub(super) fn view<'a>(
    files: &'a [(&'static str, String); 6],
    identity: &'a SetupIdentity,
) -> SetupEmissionView<'a> {
    SetupEmissionView { files, identity }
}
fn invariant(message: &str) -> OutputError {
    OutputError::Infrastructure(message.into())
}
fn range(ranges: &[Range<usize>], index: usize, text: &str) -> Result<Range<usize>, OutputError> {
    let r = ranges
        .get(index)
        .ok_or_else(|| invariant("missing setup emission range"))?;
    if r.start >= r.end
        || r.end > text.len()
        || !text.is_char_boundary(r.start)
        || !text.is_char_boundary(r.end)
    {
        return Err(invariant("invalid setup emission range"));
    }
    Ok(r.clone())
}
fn operation(op: &Operation, hardware: usize) -> Option<SetupOperation> {
    match op {
        Operation::CsrClear {
            authority: 0,
            register,
            mask: 2,
        } if register == "sstatus" => Some(SetupOperation::ClearSstatusSie),
        Operation::CsrWrite {
            authority: 0,
            register,
            value: 0,
        } if register == "sie" => Some(SetupOperation::WriteSieZero),
        Operation::InstallTrap {
            authority: 0,
            handler,
        } if *handler == hardware as u64 => Some(SetupOperation::InstallTrap { handler: hardware }),
        _ => None,
    }
}
pub(super) fn build(
    pair: &CheckedPair,
    helper_count: usize,
    function_ranges: &[Range<usize>],
    primitive_ranges: &[Range<usize>],
    abi_ranges: &[Range<usize>],
    c: &str,
    assembly: &str,
) -> Result<Result<SetupIdentity, SetupProfileUnsupported>, OutputError> {
    if pair.program.profile != Profile::V1 {
        return Ok(Err(SetupProfileUnsupported::Revision {
            profile: pair.program.profile,
        }));
    }
    for id in 0..pair.program.functions.len() {
        if !pair.program.entries.contains(&id) {
            return Ok(Err(SetupProfileUnsupported::AdditionalDefinition {
                function: id,
            }));
        }
    }
    if helper_count != 0 {
        return Ok(Err(SetupProfileUnsupported::GeneratedHelpers {
            count: helper_count,
        }));
    }
    for p in &pair.program.primitives {
        if operation(&p.operation, pair.program.entries[1]).is_none() {
            return Ok(Err(SetupProfileUnsupported::NonSetupPrimitive {
                primitive: p.id,
            }));
        }
    }
    // These bounds follow from the checked distinct roles and unique mandatory primitive keys.
    // Recheck before the small fixed-profile allocations rather than widening the profile.
    if pair.program.functions.len() != 3 || pair.program.primitives.len() != 3 {
        return Err(invariant("checked setup declaration inventory changed"));
    }
    let roles = [SetupRole::Boot, SetupRole::Hardware, SetupRole::Language];
    let mut functions = Vec::with_capacity(3);
    let mut abi = Vec::with_capacity(3);
    let symbols = [
        "anl_boot_entry",
        "anl_boot_hardware_entry",
        "anl_boot_language_entry",
    ];
    for (index, role) in roles.into_iter().enumerate() {
        let id = pair.program.entries[index];
        let f = pair
            .program
            .functions
            .get(id)
            .ok_or_else(|| invariant("missing setup role"))?;
        let effects = pair
            .program
            .effects
            .get(id)
            .ok_or_else(|| invariant("missing setup role effects"))?;
        functions.push(SetupFunction {
            id,
            role,
            symbol: format!("anl_boot_f{id}"),
            params: f.params.clone(),
            result: f.result,
            effects: effects.clone(),
            c_range: range(function_ranges, id, c)?,
        });
        abi.push(SetupAbi {
            role,
            function: id,
            stack: usize::from(index != 0),
            symbol: symbols[index],
            assembly_range: range(abi_ranges, index, assembly)?,
        });
    }
    let mut primitives = Vec::with_capacity(3);
    for (index, p) in pair.program.primitives.iter().enumerate() {
        primitives.push(SetupPrimitive {
            id: p.id,
            operation: operation(&p.operation, pair.program.entries[1])
                .ok_or_else(|| invariant("setup operation eligibility changed"))?,
            symbol: format!("anl_boot_f{}", p.id),
            params: p.params.clone(),
            result: p.result,
            effects: p.effects.clone(),
            c_range: range(primitive_ranges, index, c)?,
        });
    }
    Ok(Ok(SetupIdentity {
        helper_count,
        functions: functions
            .try_into()
            .map_err(|_| invariant("setup role count changed"))?,
        primitives,
        abi: abi
            .try_into()
            .map_err(|_| invariant("setup ABI count changed"))?,
    }))
}
