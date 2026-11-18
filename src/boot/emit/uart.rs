//! Checked V3 emission identity; no native I/O, frame or value-flow permit.
use super::super::{CheckedPair, Operation, Profile};
use crate::{bounded::OutputError, types::Type, word::WordWidth};
use std::{fmt, ops::Range};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V3UartProjectionUnsupported {
    Revision { profile: Profile },
    NoUartPrimitives,
}
impl fmt::Display for V3UartProjectionUnsupported {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Revision { profile } => write!(
                out,
                "UART leaf identity does not support {}",
                profile.target()
            ),
            Self::NoUartPrimitives => out.write_str("UART leaf identity requires a UART primitive"),
        }
    }
}
impl std::error::Error for V3UartProjectionUnsupported {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UartOperation {
    Read8,
    Write8 { offset: u8 },
    IoFence,
}
/// Descriptive fields acquire identity only through the owning opaque view.
pub struct UartPrimitive {
    id: usize,
    operation: UartOperation,
    symbol: String,
    params: Vec<Type>,
    result: Type,
    effects: Vec<u64>,
    c_range: Range<usize>,
}
impl UartPrimitive {
    pub fn id(&self) -> usize {
        self.id
    }
    pub fn operation(&self) -> UartOperation {
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
    pub fn effects(&self) -> &[u64] {
        &self.effects
    }
    pub fn region(&self) -> u64 {
        0
    }
    pub fn address(&self) -> Option<u64> {
        match self.operation {
            UartOperation::Read8 => Some(0x1000_0005),
            UartOperation::Write8 { offset } => Some(0x1000_0000 + u64::from(offset)),
            UartOperation::IoFence => None,
        }
    }
    pub fn c_range(&self) -> Range<usize> {
        self.c_range.clone()
    }
}
struct SlotIdentity {
    primitive: usize,
    symbol: String,
    assembly: Range<usize>,
}
pub(super) struct Identity {
    primitives: Vec<UartPrimitive>,
    illegal: Option<SlotIdentity>,
}
/// V3-only slot identity. It cannot be converted into the existing V2 view.
pub struct V3IllegalSlotEmissionView<'a> {
    files: &'a [(&'static str, String); 6],
    identity: &'a SlotIdentity,
}
impl V3IllegalSlotEmissionView<'_> {
    pub fn profile(&self) -> Profile {
        Profile::V3
    }
    pub fn primitive(&self) -> usize {
        self.identity.primitive
    }
    pub fn authority(&self) -> u64 {
        0
    }
    pub fn symbol(&self) -> &str {
        &self.identity.symbol
    }
    pub fn params(&self) -> &[Type] {
        &[]
    }
    pub fn result(&self) -> Type {
        Type::Unit
    }
    pub fn effects(&self) -> &[u64] {
        &[0]
    }
    /// Textual definition range; not an architectural instruction length.
    pub fn assembly_range(&self) -> Range<usize> {
        self.identity.assembly.clone()
    }
    pub fn assembly(&self) -> &str {
        &self.files[3].1
    }
}
/// Exact source artifacts and checked UART rows, not an executable leaf contract.
pub struct V3UartEmissionView<'a> {
    files: &'a [(&'static str, String); 6],
    identity: &'a Identity,
}
impl<'a> V3UartEmissionView<'a> {
    pub fn profile(&self) -> Profile {
        Profile::V3
    }
    pub fn primitives(&self) -> &[UartPrimitive] {
        &self.identity.primitives
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
    pub fn illegal_slot(&self) -> Option<V3IllegalSlotEmissionView<'a>> {
        self.identity
            .illegal
            .as_ref()
            .map(|identity| V3IllegalSlotEmissionView {
                files: self.files,
                identity,
            })
    }
}
pub(super) fn view<'a>(
    files: &'a [(&'static str, String); 6],
    identity: &'a Identity,
) -> V3UartEmissionView<'a> {
    V3UartEmissionView { files, identity }
}
fn invariant(reason: &str) -> OutputError {
    OutputError::Infrastructure(reason.into())
}
fn checked_range(range: &Range<usize>, text: &str) -> Result<Range<usize>, OutputError> {
    if range.start >= range.end || text.get(range.clone()).is_none() {
        return Err(invariant("invalid UART identity emission range"));
    }
    Ok(range.clone())
}
pub(super) fn build(
    pair: &CheckedPair,
    primitive_ranges: &[Range<usize>],
    c: &str,
    assembly: &str,
    illegal_range: Option<&(usize, Range<usize>)>,
) -> Result<Result<Identity, V3UartProjectionUnsupported>, OutputError> {
    if pair.program.profile != Profile::V3 {
        return Ok(Err(V3UartProjectionUnsupported::Revision {
            profile: pair.program.profile,
        }));
    }
    let count = pair
        .program
        .primitives
        .iter()
        .filter(|p| {
            matches!(
                p.operation,
                Operation::Read8 { .. } | Operation::Write8 { .. } | Operation::Fence { .. }
            )
        })
        .count();
    if count == 0 {
        return Ok(Err(V3UartProjectionUnsupported::NoUartPrimitives));
    }
    if count > 7 {
        return Err(invariant(
            "checked UART primitive count exceeds closed profile",
        ));
    }
    let mut primitives: Vec<UartPrimitive> = Vec::with_capacity(count);
    let mut illegal = None;
    for (index, p) in pair.program.primitives.iter().enumerate() {
        let operation = match p.operation {
            Operation::Read8 {
                region: 0,
                offset: 5,
            } => Some(UartOperation::Read8),
            Operation::Write8 { region: 0, offset } if offset <= 4 => Some(UartOperation::Write8 {
                offset: offset as u8,
            }),
            Operation::Fence { region: 0 } => Some(UartOperation::IoFence),
            Operation::Read8 { .. } | Operation::Write8 { .. } | Operation::Fence { .. } => {
                return Err(invariant("checked UART operation exceeds closed profile"));
            }
            Operation::IllegalInstruction { authority } => {
                if authority != 0
                    || !p.params.is_empty()
                    || p.result != Type::Unit
                    || p.effects != [0]
                    || illegal.is_some()
                {
                    return Err(invariant("checked V3 illegal-slot identity changed"));
                }
                let (id, range) = illegal_range
                    .ok_or_else(|| invariant("V3 illegal slot lacks emission range"))?;
                if *id != p.id {
                    return Err(invariant("V3 illegal slot emission ID differs"));
                }
                illegal = Some(SlotIdentity {
                    primitive: p.id,
                    symbol: format!("anl_boot_f{}", p.id),
                    assembly: checked_range(range, assembly)?,
                });
                None
            }
            _ => None,
        };
        let Some(operation) = operation else {
            continue;
        };
        let byte = Type::Word(WordWidth::U8);
        let valid_params = if matches!(operation, UartOperation::Write8 { .. }) {
            p.params == [byte]
        } else {
            p.params.is_empty()
        };
        let result = if operation == UartOperation::Read8 {
            byte
        } else {
            Type::Unit
        };
        if !valid_params
            || p.result != result
            || p.effects != [1]
            || primitives.iter().any(|row| row.operation == operation)
        {
            return Err(invariant("checked UART signature or key changed"));
        }
        let range = primitive_ranges
            .get(index)
            .ok_or_else(|| invariant("UART primitive emission range is absent"))?;
        primitives.push(UartPrimitive {
            id: p.id,
            operation,
            symbol: format!("anl_boot_f{}", p.id),
            params: p.params.clone(),
            result: p.result,
            effects: p.effects.clone(),
            c_range: checked_range(range, c)?,
        });
    }
    if illegal.is_some() != illegal_range.is_some() {
        return Err(invariant("V3 illegal slot range has no checked row"));
    }
    Ok(Ok(Identity {
        primitives,
        illegal,
    }))
}
