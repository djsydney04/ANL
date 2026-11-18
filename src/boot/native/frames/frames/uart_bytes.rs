//! Conditional native low-byte correspondence; no call summary or source bridge.
use super::*;
use anl::boot::UartOperation;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UartBytePhase {
    Entry,
    Transfer,
    Completion,
}

#[derive(Debug)]
pub struct UartByteError {
    pub class: ErrorClass,
    pub phase: UartBytePhase,
    pub reason: &'static str,
    pub primitive: Option<usize>,
    pub contribution: Option<ContributionId>,
    pub word: Option<WordId>,
    pub pc: Option<u64>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UartByteRelation {
    ReadResponseLow8,
    WriteArgumentLow8AndUnitZero,
    FenceAndUnitZero,
}

/// Describes the relation only for the exact held footprint's selected leaf.
pub struct UartByteLeaf {
    primitive: usize,
    contribution: ContributionId,
    effect: WordId,
    return_word: WordId,
    relation: UartByteRelation,
}
impl UartByteLeaf {
    pub fn primitive(&self) -> usize {
        self.primitive
    }
    pub fn contribution(&self) -> ContributionId {
        self.contribution
    }
    pub fn effect_word(&self) -> WordId {
        self.effect
    }
    pub fn return_word(&self) -> WordId {
        self.return_word
    }
    pub fn relation(&self) -> UartByteRelation {
        self.relation
    }
}

#[derive(Clone, Copy, Debug)]
pub struct UartByteCounters {
    input: Counters,
    composed: Counters,
}
impl UartByteCounters {
    pub fn input(&self) -> Counters {
        self.input
    }
    pub fn composed(&self) -> Counters {
        self.composed
    }
    pub fn added_created_states(&self) -> usize {
        self.composed.created_states - self.input.created_states
    }
    pub fn added_transfer_evaluations(&self) -> usize {
        self.composed.transfer_evaluations - self.input.transfer_evaluations
    }
    pub fn added_rows(&self) -> usize {
        self.composed.charged_rows - self.input.charged_rows
    }
}

/// Borrows the immutable footprint; no constructor accepts descriptive facts.
pub struct UartByteInspection<'e, 'a> {
    footprint: &'e UartLeafInspection<'a>,
    leaves: Vec<UartByteLeaf>,
    counters: UartByteCounters,
}
impl<'e, 'a> UartByteInspection<'e, 'a> {
    pub fn footprint(&self) -> &'e UartLeafInspection<'a> {
        self.footprint
    }
    pub fn leaves(&self) -> &[UartByteLeaf] {
        &self.leaves
    }
    pub fn counters(&self) -> UartByteCounters {
        self.counters
    }
    pub fn premise_profile(&self) -> &'static str {
        "uart_leaf_low8_instruction_refinement"
    }
    pub fn abi_extension_bits_established(&self) -> bool {
        false
    }
    pub fn source_correspondence_established(&self) -> bool {
        false
    }
    pub fn handler_calls_established(&self) -> bool {
        false
    }
    pub fn native_admitted(&self) -> bool {
        false
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Origin {
    EntryArgument(usize),
    DeviceResponse(usize, WordId),
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum ByteFact {
    Unknown,
    Constant(u8),
    Origin(Origin),
}
struct ByteState {
    registers: [ByteFact; 32],
    memory: BTreeMap<i64, ByteFact>,
}
type ByteResult<T> = std::result::Result<T, UartByteError>;

fn failure(
    class: ErrorClass,
    phase: UartBytePhase,
    reason: &'static str,
    leaf: &UartLeaf,
    instruction: Option<Instruction>,
) -> UartByteError {
    UartByteError {
        class,
        phase,
        reason,
        primitive: Some(leaf.primitive()),
        contribution: Some(leaf.contribution()),
        word: instruction.map(|i| i.id),
        pc: instruction.map(|i| i.pc),
    }
}
struct ByteBudget {
    counts: Counters,
    live: usize,
}
impl ByteBudget {
    fn examine(
        &mut self,
        leaf: &UartLeaf,
        phase: UartBytePhase,
        instruction: Option<Instruction>,
    ) -> ByteResult<()> {
        if self.counts.transfer_evaluations >= MAX_TRANSFERS {
            return Err(failure(
                ErrorClass::Resource,
                phase,
                "composed byte transfer limit exceeded",
                leaf,
                instruction,
            ));
        }
        self.counts.transfer_evaluations += 1;
        Ok(())
    }
    fn facts(
        &mut self,
        count: usize,
        leaf: &UartLeaf,
        phase: UartBytePhase,
        instruction: Option<Instruction>,
    ) -> ByteResult<()> {
        let total = self
            .live
            .checked_add(count)
            .filter(|&n| n <= MAX_FACTS)
            .ok_or_else(|| {
                failure(
                    ErrorClass::Resource,
                    phase,
                    "composed byte fact limit exceeded",
                    leaf,
                    instruction,
                )
            })?;
        self.live = total;
        self.counts.peak_facts = self.counts.peak_facts.max(total);
        Ok(())
    }
    fn release(
        &mut self,
        count: usize,
        leaf: &UartLeaf,
        instruction: Option<Instruction>,
    ) -> ByteResult<()> {
        self.live = self.live.checked_sub(count).ok_or_else(|| {
            failure(
                ErrorClass::Infrastructure,
                UartBytePhase::Transfer,
                "byte fact accounting underflow",
                leaf,
                instruction,
            )
        })?;
        Ok(())
    }
    fn state(&mut self, leaf: &UartLeaf) -> ByteResult<ByteState> {
        if self.counts.created_states >= MAX_STATES {
            return Err(failure(
                ErrorClass::Resource,
                UartBytePhase::Entry,
                "composed byte state limit exceeded",
                leaf,
                None,
            ));
        }
        self.facts(32, leaf, UartBytePhase::Entry, None)?;
        self.counts.created_states += 1;
        let mut registers = [ByteFact::Unknown; 32];
        registers[0] = ByteFact::Constant(0);
        if matches!(leaf.operation(), UartOperation::Write8 { .. }) {
            registers[10] = ByteFact::Origin(Origin::EntryArgument(leaf.primitive()));
        }
        Ok(ByteState {
            registers,
            memory: BTreeMap::new(),
        })
    }
    fn row(&mut self, leaf: &UartLeaf) -> ByteResult<()> {
        if self.counts.charged_rows >= MAX_WITNESS_ROWS {
            return Err(failure(
                ErrorClass::Resource,
                UartBytePhase::Completion,
                "composed byte witness limit exceeded",
                leaf,
                None,
            ));
        }
        self.counts.charged_rows += 1;
        Ok(())
    }
}

fn register_value(
    instruction: Instruction,
    decoded: Decoded,
    state: &ByteState,
) -> Option<(u8, ByteFact)> {
    let value = match decoded.operands {
        Operands::Upper { rd, immediate } => (
            rd,
            match decoded.operation {
                Op::Lui => ByteFact::Constant(immediate as u8),
                Op::Auipc => {
                    ByteFact::Constant(instruction.pc.wrapping_add(immediate as u64) as u8)
                }
                _ => ByteFact::Unknown,
            },
        ),
        Operands::Immediate { rd, rs1, immediate } => {
            let source = state.registers[usize::from(rs1)];
            (
                rd,
                match (decoded.operation, source) {
                    (Op::Addi, ByteFact::Constant(n)) => {
                        ByteFact::Constant(n.wrapping_add(immediate as u8))
                    }
                    (Op::Addi, fact) if immediate == 0 => fact,
                    (Op::Andi, fact) if immediate as u8 == u8::MAX => fact,
                    (Op::Andi, ByteFact::Constant(n)) => ByteFact::Constant(n & immediate as u8),
                    _ => ByteFact::Unknown,
                },
            )
        }
        Operands::Registers { rd, .. }
        | Operands::Load { rd, .. }
        | Operands::Jump { rd, .. }
        | Operands::Indirect { rd, .. }
        | Operands::Csr { rd, .. } => (rd, ByteFact::Unknown),
        _ => return None,
    };
    Some(value)
}

fn require_origin(
    actual: ByteFact,
    expected: Origin,
    leaf: &UartLeaf,
    instruction: Instruction,
    phase: UartBytePhase,
) -> ByteResult<()> {
    if actual != ByteFact::Origin(expected) {
        return Err(failure(
            ErrorClass::Unsupported,
            phase,
            "required native byte origin is not established",
            leaf,
            Some(instruction),
        ));
    }
    Ok(())
}

fn frame_access(
    row: MemoryObservation,
    instruction: Instruction,
    decoded: Decoded,
    state: &mut ByteState,
    budget: &mut ByteBudget,
    leaf: &UartLeaf,
) -> ByteResult<Option<(u8, ByteFact)>> {
    let bad = || {
        failure(
            ErrorClass::Infrastructure,
            UartBytePhase::Transfer,
            "held frame observation disagrees with its instruction",
            leaf,
            Some(instruction),
        )
    };
    if row.word != instruction.id || !matches!(row.width, 1 | 2 | 4 | 8) {
        return Err(bad());
    }
    match (row.access, decoded.effect, decoded.operands) {
        (Access::Load, Effect::Load { bytes, .. }, Operands::Load { rd, .. })
            if row.width == bytes && row.discarded_load == (rd == 0) =>
        {
            Ok(Some((
                rd,
                state
                    .memory
                    .get(&row.offset)
                    .copied()
                    .unwrap_or(ByteFact::Unknown),
            )))
        }
        (Access::Store, Effect::Store { bytes }, Operands::Store { source, .. })
            if row.width == bytes && !row.discarded_load =>
        {
            let fact = state.registers[usize::from(source)];
            for offset in 0..row.width {
                budget.examine(leaf, UartBytePhase::Transfer, Some(instruction))?;
                let address = row.offset.checked_add(i64::from(offset)).ok_or_else(bad)?;
                if state.memory.remove(&address).is_some() {
                    budget.release(1, leaf, Some(instruction))?;
                }
            }
            // Upper bytes remain unknown even when the source happens to be a byte.
            if fact != ByteFact::Unknown {
                budget.facts(1, leaf, UartBytePhase::Transfer, Some(instruction))?;
                state.memory.insert(row.offset, fact);
            }
            Ok(None)
        }
        _ => Err(bad()),
    }
}

fn device_event(
    event: IoObservation,
    instruction: Instruction,
    decoded: Decoded,
    state: &ByteState,
    leaf: &UartLeaf,
) -> ByteResult<Option<(u8, ByteFact)>> {
    let bad = || {
        failure(
            ErrorClass::Infrastructure,
            UartBytePhase::Transfer,
            "held I/O observation disagrees with its UART leaf",
            leaf,
            Some(instruction),
        )
    };
    if event.word() != instruction.id || event.word() != leaf.effect_word() {
        return Err(bad());
    }
    match (
        leaf.operation(),
        event.event(),
        decoded.operation,
        decoded.effect,
        decoded.operands,
    ) {
        (
            UartOperation::Read8,
            IoEvent::ReadByte {
                address: 0x1000_0005,
                width: 1,
                value: Fact::Unknown,
                discarded,
            },
            Op::Lbu,
            Effect::Load {
                bytes: 1,
                sign_extend: false,
            },
            Operands::Load { rd, .. },
        ) if discarded == (rd == 0) => Ok(Some((
            rd,
            ByteFact::Origin(Origin::DeviceResponse(leaf.primitive(), instruction.id)),
        ))),
        (
            UartOperation::Write8 { offset },
            IoEvent::WriteByte {
                address,
                width: 1,
                value: Fact::Unknown,
            },
            Op::Sb,
            Effect::Store { bytes: 1 },
            Operands::Store { source, .. },
        ) if offset <= 4 && address == 0x1000_0000 + u64::from(offset) => {
            require_origin(
                state.registers[usize::from(source)],
                Origin::EntryArgument(leaf.primitive()),
                leaf,
                instruction,
                UartBytePhase::Transfer,
            )?;
            Ok(None)
        }
        (
            UartOperation::IoFence,
            IoEvent::Fence {
                encoding: 0x0ff0_000f,
                mode: 0,
                predecessors: 15,
                successors: 15,
                rd: 0,
                rs1: 0,
            },
            Op::Fence,
            Effect::Fence,
            Operands::None,
        ) if instruction.raw == 0x0ff0_000f => Ok(None),
        _ => Err(bad()),
    }
}

/// Checks low-byte flow only; full ABI extension and ANL caller bridges remain open.
pub fn inspect_uart_bytes_v3<'e, 'a>(
    footprint: &'e UartLeafInspection<'a>,
) -> ByteResult<UartByteInspection<'e, 'a>> {
    let input = footprint.counters();
    let mut budget = ByteBudget {
        counts: input,
        live: input.retained_facts,
    };
    let view = footprint.machine().inventory();
    let words = view.instructions();
    let held_leaves = footprint.leaves();
    // A successful opaque footprint has one through seven selected identities.
    if held_leaves.is_empty() || held_leaves.len() > 7 {
        return Err(UartByteError {
            class: ErrorClass::Infrastructure,
            phase: UartBytePhase::Entry,
            reason: "held UART leaf count changed",
            primitive: None,
            contribution: None,
            word: None,
            pc: None,
        });
    }
    let mut leaves = Vec::with_capacity(held_leaves.len());
    for leaf in held_leaves {
        budget.examine(leaf, UartBytePhase::Entry, None)?;
        let bad_entry = || {
            failure(
                ErrorClass::Infrastructure,
                UartBytePhase::Entry,
                "held UART body or observation range changed",
                leaf,
                None,
            )
        };
        let contribution = view
            .text()
            .contributions()
            .get(leaf.contribution())
            .ok_or_else(bad_entry)?;
        let count = usize::try_from(contribution.image.size / 4).map_err(|_| bad_entry())?;
        let end = leaf.return_word().checked_add(1).ok_or_else(bad_entry)?;
        let start = end.checked_sub(count).ok_or_else(bad_entry)?;
        let body = words
            .get(start..end)
            .filter(|body| !body.is_empty())
            .ok_or_else(bad_entry)?;
        if !contribution.image.size.is_multiple_of(4) || body[0].pc != contribution.image.value {
            return Err(bad_entry());
        }
        let memory = footprint
            .frame_accesses()
            .get(leaf.frame_access_indices())
            .ok_or_else(bad_entry)?;
        let io = footprint
            .io()
            .get(leaf.io_indices())
            .filter(|io| io.len() == 1)
            .ok_or_else(bad_entry)?;
        let mut memory_cursor = 0;
        let mut io_cursor = 0;
        let mut state = budget.state(leaf)?;
        for (offset, &instruction) in body.iter().enumerate() {
            budget.examine(leaf, UartBytePhase::Transfer, Some(instruction))?;
            let bad = || {
                failure(
                    ErrorClass::Infrastructure,
                    UartBytePhase::Transfer,
                    "held straight-line instruction or observation order changed",
                    leaf,
                    Some(instruction),
                )
            };
            let pc = contribution
                .image
                .value
                .checked_add((offset as u64) * 4)
                .ok_or_else(bad)?;
            if instruction.id != start + offset
                || instruction.pc != pc
                || instruction.contribution != leaf.contribution()
            {
                return Err(bad());
            }
            let decoded = instruction.ordinary().ok_or_else(bad)?;
            let final_word = instruction.id == leaf.return_word();
            if matches!(
                decoded.operands,
                Operands::Branch { .. } | Operands::Jump { .. } | Operands::Csr { .. }
            ) || (matches!(decoded.operands, Operands::Indirect { .. }) != final_word)
                || (final_word
                    && (decoded.operation != Op::Jalr
                        || decoded.operands
                            != (Operands::Indirect {
                                rd: 0,
                                base: 1,
                                offset: 0,
                            })))
            {
                return Err(bad());
            }
            let next_memory = memory.get(memory_cursor);
            let next_io = io.get(io_cursor);
            if next_memory.is_some_and(|row| row.word < instruction.id)
                || next_io.is_some_and(|row| row.word() < instruction.id)
            {
                return Err(bad());
            }
            let frame = next_memory.filter(|row| row.word == instruction.id);
            let event = next_io.filter(|row| row.word() == instruction.id);
            if frame.is_some() && event.is_some() {
                return Err(bad());
            }
            let mut destination = register_value(instruction, decoded, &state);
            match (decoded.effect, frame, event) {
                (Effect::Load { .. } | Effect::Store { .. }, Some(row), None) => {
                    destination =
                        frame_access(*row, instruction, decoded, &mut state, &mut budget, leaf)?;
                    memory_cursor += 1;
                }
                (Effect::Load { .. } | Effect::Store { .. } | Effect::Fence, None, Some(event)) => {
                    destination = device_event(*event, instruction, decoded, &state, leaf)?;
                    io_cursor += 1;
                }
                (Effect::None, None, None) => {}
                _ => return Err(bad()),
            }
            if let Some((rd, fact)) = destination
                && rd != 0
            {
                state.registers[usize::from(rd)] = fact;
            }
        }
        budget.examine(leaf, UartBytePhase::Completion, None)?;
        let instruction = body[count - 1];
        if memory_cursor != memory.len() || io_cursor != io.len() {
            return Err(failure(
                ErrorClass::Infrastructure,
                UartBytePhase::Completion,
                "held UART observations were not consumed exactly once",
                leaf,
                Some(instruction),
            ));
        }
        let relation = match leaf.operation() {
            UartOperation::Read8 => {
                require_origin(
                    state.registers[10],
                    Origin::DeviceResponse(leaf.primitive(), leaf.effect_word()),
                    leaf,
                    instruction,
                    UartBytePhase::Completion,
                )?;
                UartByteRelation::ReadResponseLow8
            }
            UartOperation::Write8 { .. } | UartOperation::IoFence => {
                let final_state = footprint.state(leaf.return_word()).ok_or_else(|| {
                    failure(
                        ErrorClass::Infrastructure,
                        UartBytePhase::Completion,
                        "held UART return state is absent",
                        leaf,
                        Some(instruction),
                    )
                })?;
                match final_state.registers()[10] {
                    Fact::Const(0) => {}
                    Fact::Const(_) => {
                        return Err(failure(
                            ErrorClass::Infrastructure,
                            UartBytePhase::Completion,
                            "native unit return is nonzero",
                            leaf,
                            Some(instruction),
                        ));
                    }
                    _ => {
                        return Err(failure(
                            ErrorClass::Unsupported,
                            UartBytePhase::Completion,
                            "native unit return zero is not established",
                            leaf,
                            Some(instruction),
                        ));
                    }
                }
                if leaf.operation() == UartOperation::IoFence {
                    UartByteRelation::FenceAndUnitZero
                } else {
                    UartByteRelation::WriteArgumentLow8AndUnitZero
                }
            }
        };
        budget.row(leaf)?;
        leaves.push(UartByteLeaf {
            primitive: leaf.primitive(),
            contribution: leaf.contribution(),
            effect: leaf.effect_word(),
            return_word: leaf.return_word(),
            relation,
        });
        budget.release(32 + state.memory.len(), leaf, None)?;
    }
    Ok(UartByteInspection {
        footprint,
        leaves,
        counters: UartByteCounters {
            input,
            composed: budget.counts,
        },
    })
}
