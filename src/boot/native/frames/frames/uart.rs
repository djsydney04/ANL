//! Exact UART footprint and conditional normal-return frames; no value or call summary.
use super::*;
use crate::machine::text::TextInspection;
use crate::machine::{MachineError, V3UartMachineInspection, inspect_uart_machine_v3};
use anl::boot::{Bundle, UartOperation, UartPrimitive, V3UartProjectionUnsupported};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UartPhase {
    Identity,
    ForbiddenEffects,
    Shape,
    FinalFootprint,
}
#[derive(Debug)]
pub struct UartDiagnostic {
    pub class: ErrorClass,
    pub phase: UartPhase,
    pub reason: &'static str,
    pub primitive: Option<usize>,
    pub contribution: Option<ContributionId>,
    pub word: Option<WordId>,
    pub pc: Option<u64>,
}
#[derive(Debug)]
pub enum UartInspectionError {
    Projection(V3UartProjectionUnsupported),
    Machine(MachineError),
    Frame(FrameError),
    Policy(UartDiagnostic),
}
impl From<FrameError> for UartInspectionError {
    fn from(error: FrameError) -> Self {
        Self::Frame(error)
    }
}
type UartResult<T> = std::result::Result<T, UartInspectionError>;

/// Descriptive events never carry an ANL argument/result correspondence claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IoEvent {
    ReadByte {
        address: u64,
        width: u8,
        value: Fact,
        discarded: bool,
    },
    WriteByte {
        address: u64,
        width: u8,
        value: Fact,
    },
    Fence {
        encoding: u32,
        mode: u8,
        predecessors: u8,
        successors: u8,
        rd: u8,
        rs1: u8,
    },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IoObservation {
    word: WordId,
    event: IoEvent,
}
impl IoObservation {
    pub fn word(&self) -> WordId {
        self.word
    }
    pub fn event(&self) -> IoEvent {
        self.event
    }
}
/// Local depth applies only to normally completing instruction/device prefixes,
/// with aligned nonwrapping entry SP/RA and writable own-frame storage disjoint
/// from the device, under the local instruction transfer/refinement premises.
/// It promises neither device completion nor that an ordinary return occurs.
pub struct UartLeaf {
    primitive: usize,
    operation: UartOperation,
    contribution: ContributionId,
    effect: WordId,
    return_word: WordId,
    depth: u64,
    memory: Range<usize>,
    io: Range<usize>,
}
impl UartLeaf {
    pub fn primitive(&self) -> usize {
        self.primitive
    }
    pub fn operation(&self) -> UartOperation {
        self.operation
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
    pub fn local_depth(&self) -> u64 {
        self.depth
    }
    pub fn frame_access_indices(&self) -> Range<usize> {
        self.memory.clone()
    }
    pub fn io_indices(&self) -> Range<usize> {
        self.io.clone()
    }
    pub fn premise_profile(&self) -> &'static str {
        "uart_leaf_normal_instruction_refinement"
    }
}
pub struct UartLeafInspection<'a> {
    machine: V3UartMachineInspection<'a>,
    data: FrameData,
    leaves: Vec<UartLeaf>,
}
impl<'a> UartLeafInspection<'a> {
    pub fn machine(&self) -> &V3UartMachineInspection<'a> {
        &self.machine
    }
    pub fn leaves(&self) -> &[UartLeaf] {
        &self.leaves
    }
    pub fn frame_accesses(&self) -> &[MemoryObservation] {
        &self.data.memory
    }
    pub fn io(&self) -> &[IoObservation] {
        &self.data.io
    }
    pub fn returns(&self) -> &[ReturnEvidence] {
        &self.data.returns
    }
    pub fn state(&self, word: WordId) -> Option<&State> {
        self.data.states.get(word).and_then(Option::as_deref)
    }
    pub fn counters(&self) -> Counters {
        self.data.counters
    }
    pub fn unchecked_contributions(&self) -> impl Iterator<Item = ContributionId> + '_ {
        (0..self.machine.inventory().text().contributions().len())
            .filter(|id| !self.leaves.iter().any(|leaf| leaf.contribution == *id))
    }
    pub fn argument_result_provenance_established(&self) -> bool {
        false
    }
    pub fn source_correspondence_established(&self) -> bool {
        false
    }
    pub fn handler_calls_established(&self) -> bool {
        false
    }
    pub fn handler_stack_bound_established(&self) -> bool {
        false
    }
    pub fn delivery_established(&self) -> bool {
        false
    }
    pub fn nested_fault_safety_established(&self) -> bool {
        false
    }
    pub fn formal_native_correspondence(&self) -> bool {
        false
    }
    pub fn native_admitted(&self) -> bool {
        false
    }
}

pub(super) struct LeafRule {
    primitive: usize,
    operation: UartOperation,
    contribution: ContributionId,
    words: Range<usize>,
}
fn diagnostic(
    class: ErrorClass,
    phase: UartPhase,
    reason: &'static str,
    primitive: Option<usize>,
    contribution: Option<ContributionId>,
    instruction: Option<Instruction>,
    pc: Option<u64>,
) -> UartInspectionError {
    UartInspectionError::Policy(UartDiagnostic {
        class,
        phase,
        reason,
        primitive,
        contribution,
        word: instruction.map(|i| i.id),
        pc: instruction.map(|i| i.pc).or(pc),
    })
}
fn fail(
    class: ErrorClass,
    phase: UartPhase,
    reason: &'static str,
    rule: &LeafRule,
    instruction: Option<Instruction>,
) -> UartInspectionError {
    diagnostic(
        class,
        phase,
        reason,
        Some(rule.primitive),
        Some(rule.contribution),
        instruction,
        None,
    )
}
fn examine(
    budget: &mut Budget,
    phase: UartPhase,
    primitive: usize,
    contribution: Option<ContributionId>,
    instruction: Option<Instruction>,
    pc: Option<u64>,
) -> UartResult<()> {
    budget.evaluation(Stage::Index).map_err(|e| {
        diagnostic(
            e.class,
            phase,
            e.reason,
            Some(primitive),
            contribution,
            instruction,
            pc,
        )
    })
}
fn row(
    budget: &mut Budget,
    phase: UartPhase,
    rule: &LeafRule,
    instruction: Option<Instruction>,
    pc: Option<u64>,
) -> UartResult<()> {
    budget.row(Stage::Index).map_err(|e| {
        diagnostic(
            e.class,
            phase,
            e.reason,
            Some(rule.primitive),
            Some(rule.contribution),
            instruction,
            pc,
        )
    })
}
fn bind(
    view: &MachineInventoryView<'_, '_>,
    primitives: &[UartPrimitive],
    budget: &mut Budget,
) -> UartResult<Vec<LeafRule>> {
    if primitives.is_empty() || primitives.len() > 7 {
        return Err(diagnostic(
            ErrorClass::Infrastructure,
            UartPhase::Identity,
            "opaque UART identity count changed",
            None,
            None,
            None,
            None,
        ));
    }
    let mut rules: Vec<LeafRule> = Vec::with_capacity(primitives.len());
    let mut first_unsupported = None;
    for primitive in primitives {
        let id = primitive.id();
        examine(budget, UartPhase::Identity, id, None, None, None)?;
        let mut found = None;
        for (contribution, c) in view.text().contributions().iter().enumerate() {
            let at = Some(contribution);
            examine(
                budget,
                UartPhase::Identity,
                id,
                at,
                None,
                Some(c.image.value),
            )?;
            let mut object_alias = None;
            let mut image_alias = None;
            for (aliases, matched) in [
                (&c.aliases, &mut object_alias),
                (&c.image_aliases, &mut image_alias),
            ] {
                for alias in aliases {
                    examine(
                        budget,
                        UartPhase::Identity,
                        id,
                        at,
                        None,
                        Some(c.image.value),
                    )?;
                    if alias.name == primitive.symbol()
                        && matched.replace((alias.binding, alias.visibility)).is_some()
                    {
                        return Err(diagnostic(
                            ErrorClass::Infrastructure,
                            UartPhase::Identity,
                            "duplicate canonical UART alias",
                            Some(id),
                            at,
                            None,
                            Some(c.image.value),
                        ));
                    }
                }
            }
            if object_alias.is_none() && image_alias.is_none() {
                continue;
            }
            if object_alias.is_none()
                || image_alias.is_none()
                || object_alias != image_alias
                || c.object != 1
            {
                return Err(diagnostic(
                    ErrorClass::Infrastructure,
                    UartPhase::Identity,
                    "UART object/image identity or producer contradicts its source row",
                    Some(id),
                    at,
                    None,
                    Some(c.image.value),
                ));
            }
            if found.replace(contribution).is_some() {
                return Err(diagnostic(
                    ErrorClass::Infrastructure,
                    UartPhase::Identity,
                    "canonical UART identity has multiple contributions",
                    Some(id),
                    at,
                    None,
                    Some(c.image.value),
                ));
            }
            // C emits these functions static. The illegal slot has a separate global contract.
            if (object_alias != Some((0, 0)) || c.aliases.len() != 1 || c.image_aliases.len() != 1)
                && first_unsupported.is_none()
            {
                first_unsupported = Some(diagnostic(
                    ErrorClass::Unsupported,
                    UartPhase::Identity,
                    "UART alias shape or localization is not implemented",
                    Some(id),
                    at,
                    None,
                    Some(c.image.value),
                ));
            }
        }
        let contribution = found.ok_or_else(|| {
            diagnostic(
                ErrorClass::Infrastructure,
                UartPhase::Identity,
                "canonical UART identity is absent",
                Some(id),
                None,
                None,
                None,
            )
        })?;
        for previous in &rules {
            examine(
                budget,
                UartPhase::Identity,
                id,
                Some(contribution),
                None,
                Some(view.text().contributions()[contribution].image.value),
            )?;
            if previous.contribution == contribution {
                return Err(diagnostic(
                    ErrorClass::Infrastructure,
                    UartPhase::Identity,
                    "distinct UART identities share a native contribution",
                    Some(id),
                    Some(contribution),
                    None,
                    Some(view.text().contributions()[contribution].image.value),
                ));
            }
        }
        let rule = LeafRule {
            primitive: id,
            operation: primitive.operation(),
            contribution,
            words: 0..0,
        };
        row(
            budget,
            UartPhase::Identity,
            &rule,
            None,
            Some(view.text().contributions()[contribution].image.value),
        )?;
        rules.push(rule);
    }
    if let Some(error) = first_unsupported {
        return Err(error);
    }
    Ok(rules)
}
fn forbidden(
    view: &MachineInventoryView<'_, '_>,
    graph: &Graph,
    rule: &mut LeafRule,
    budget: &mut Budget,
) -> UartResult<()> {
    examine(
        budget,
        UartPhase::ForbiddenEffects,
        rule.primitive,
        Some(rule.contribution),
        None,
        None,
    )?;
    let first = graph.entries[rule.contribution];
    let count = usize::try_from(view.text().contributions()[rule.contribution].image.size / 4)
        .map_err(|_| {
            fail(
                ErrorClass::Infrastructure,
                UartPhase::ForbiddenEffects,
                "UART body extent exceeds host",
                rule,
                None,
            )
        })?;
    let end = first
        .checked_add(count)
        .filter(|&n| n <= view.instructions().len())
        .ok_or_else(|| {
            fail(
                ErrorClass::Infrastructure,
                UartPhase::ForbiddenEffects,
                "UART body interval changed",
                rule,
                None,
            )
        })?;
    rule.words = first..end;
    let mut fences = 0;
    for word in rule.words.clone() {
        let instruction = view.instructions()[word];
        examine(
            budget,
            UartPhase::ForbiddenEffects,
            rule.primitive,
            Some(rule.contribution),
            Some(instruction),
            None,
        )?;
        if instruction.contribution != rule.contribution {
            return Err(fail(
                ErrorClass::Infrastructure,
                UartPhase::ForbiddenEffects,
                "UART body crosses contribution ownership",
                rule,
                Some(instruction),
            ));
        }
        let decoded = instruction.ordinary().ok_or_else(|| {
            fail(
                ErrorClass::Infrastructure,
                UartPhase::ForbiddenEffects,
                "illegal slot is forbidden in a UART leaf",
                rule,
                Some(instruction),
            )
        })?;
        if matches!(decoded.effect, Effect::Csr { .. }) {
            return Err(fail(
                ErrorClass::Infrastructure,
                UartPhase::ForbiddenEffects,
                "CSR is forbidden in a UART leaf",
                rule,
                Some(instruction),
            ));
        }
        if decoded.effect == Effect::Fence {
            fences += 1;
            if rule.operation != UartOperation::IoFence || fences > 1 {
                return Err(fail(
                    ErrorClass::Infrastructure,
                    UartPhase::ForbiddenEffects,
                    "fence contradicts the UART leaf operation",
                    rule,
                    Some(instruction),
                ));
            }
        }
    }
    Ok(())
}
fn shape(
    view: &MachineInventoryView<'_, '_>,
    graph: &Graph,
    rule: &LeafRule,
    budget: &mut Budget,
) -> UartResult<()> {
    for word in rule.words.clone() {
        let instruction = view.instructions()[word];
        examine(
            budget,
            UartPhase::Shape,
            rule.primitive,
            Some(rule.contribution),
            Some(instruction),
            None,
        )?;
        let links = graph.links[word];
        let decoded = instruction.ordinary().ok_or_else(|| {
            fail(
                ErrorClass::Infrastructure,
                UartPhase::Shape,
                "UART ordinary body changed",
                rule,
                Some(instruction),
            )
        })?;
        let last = word + 1 == rule.words.end;
        if links.transfer.is_some()
            || (last && (!links.returns || links.local.iter().any(Option::is_some)))
            || (!last
                && (links.returns
                    || links.local != [Some(word + 1), None]
                    || matches!(
                        decoded.operands,
                        Operands::Branch { .. } | Operands::Jump { .. } | Operands::Indirect { .. }
                    )))
        {
            return Err(fail(
                ErrorClass::Unsupported,
                UartPhase::Shape,
                "UART leaf requires its complete straight-line body and sole final ordinary return",
                rule,
                Some(instruction),
            ));
        }
    }
    Ok(())
}

pub(super) fn memory_event(
    rule: &LeafRule,
    instruction: Instruction,
    address: Fact,
) -> Option<IoObservation> {
    if instruction.contribution != rule.contribution {
        return None;
    }
    let Fact::Const(address) = address else {
        return None;
    };
    address.checked_add(1)?;
    let decoded = instruction.ordinary()?;
    let event = match (
        rule.operation,
        decoded.operation,
        decoded.effect,
        decoded.operands,
    ) {
        (
            UartOperation::Read8,
            Op::Lbu,
            Effect::Load {
                bytes: 1,
                sign_extend: false,
            },
            Operands::Load { rd, .. },
        ) if address == 0x1000_0005 => IoEvent::ReadByte {
            address,
            width: 1,
            value: Fact::Unknown,
            discarded: rd == 0,
        },
        (
            UartOperation::Write8 { offset },
            Op::Sb,
            Effect::Store { bytes: 1 },
            Operands::Store { .. },
        ) if offset <= 4 && address == 0x1000_0000 + u64::from(offset) => IoEvent::WriteByte {
            address,
            width: 1,
            value: Fact::Unknown,
        },
        _ => return None,
    };
    Some(IoObservation {
        word: instruction.id,
        event,
    })
}
pub(super) fn fence_event(rule: &LeafRule, instruction: Instruction) -> Option<IoObservation> {
    if rule.operation != UartOperation::IoFence
        || instruction.contribution != rule.contribution
        || instruction.raw != 0x0ff0_000f
    {
        return None;
    }
    let decoded = instruction.ordinary()?;
    if decoded.operation != Op::Fence
        || decoded.effect != Effect::Fence
        || decoded.operands != Operands::None
    {
        return None;
    }
    Some(IoObservation {
        word: instruction.id,
        event: IoEvent::Fence {
            encoding: instruction.raw,
            mode: 0,
            predecessors: 15,
            successors: 15,
            rd: 0,
            rs1: 0,
        },
    })
}
fn frontier_class(frontier: Frontier, engine: &Engine<'_, '_>) -> ErrorClass {
    match frontier.kind {
        FrontierKind::Memory { address, gap, .. } => match gap {
            MemoryGap::OutsideFrame | MemoryGap::Misaligned => ErrorClass::Infrastructure,
            MemoryGap::UnknownSp => ErrorClass::Unsupported,
            MemoryGap::NonFrameAddress => {
                if matches!(address, Fact::Const(_)) {
                    ErrorClass::Infrastructure
                } else {
                    ErrorClass::Unsupported
                }
            }
        },
        FrontierKind::SpOutsideDomain { value } => {
            if matches!(value, Fact::Const(_) | Fact::EntrySpPlus(_)) {
                ErrorClass::Infrastructure
            } else {
                ErrorClass::Unsupported
            }
        }
        FrontierKind::Csr | FrontierKind::Fence => ErrorClass::Infrastructure,
        FrontierKind::ReturnNotEstablished => {
            let Some(state) = engine.states[frontier.word].as_deref() else {
                return ErrorClass::Infrastructure;
            };
            let contradicts =
                |actual: Fact, expected: Fact| actual != Fact::Unknown && actual != expected;
            if contradicts(state.registers[2], Fact::EntrySpPlus(0))
                || contradicts(state.registers[1], Fact::EntryRegister(1))
                || (0_u8..32).any(|r| {
                    CALLEE_SAVED & (1_u32 << r) != 0
                        && contradicts(state.registers[usize::from(r)], Fact::EntryRegister(r))
                })
            {
                ErrorClass::Infrastructure
            } else {
                ErrorClass::Unsupported
            }
        }
        _ => ErrorClass::Unsupported,
    }
}
fn completed(
    engine: &mut Engine<'_, '_>,
    rule: &LeafRule,
    first_io: usize,
) -> UartResult<UartLeaf> {
    let view = engine.machine;
    let frame = engine.contributions.last().ok_or_else(|| {
        fail(
            ErrorClass::Infrastructure,
            UartPhase::FinalFootprint,
            "UART final contribution is absent",
            rule,
            None,
        )
    })?;
    examine(
        &mut engine.budget,
        UartPhase::FinalFootprint,
        rule.primitive,
        Some(rule.contribution),
        None,
        None,
    )?;
    if let Some(frontier) = engine
        .frontiers
        .get(frame.frontier_indices.start)
        .filter(|_| !frame.frontier_indices.is_empty())
    {
        return Err(fail(
            frontier_class(*frontier, engine),
            UartPhase::FinalFootprint,
            "UART frame or effect is not established at the final reached frontier",
            rule,
            Some(view.instructions()[frontier.word]),
        ));
    }
    if frame.contribution != rule.contribution
        || frame.coverage != Coverage::ClosedLocalReturns
        || frame.covered_words != rule.words.len()
        || frame.return_indices.len() != 1
    {
        return Err(fail(
            ErrorClass::Unsupported,
            UartPhase::FinalFootprint,
            "UART final pass lacks complete body coverage and one ordinary return",
            rule,
            None,
        ));
    }
    let evidence = engine.returns[frame.return_indices.start];
    if !evidence.established || evidence.word + 1 != rule.words.end {
        return Err(fail(
            ErrorClass::Infrastructure,
            UartPhase::FinalFootprint,
            "UART final return evidence changed",
            rule,
            Some(view.instructions()[evidence.word]),
        ));
    }
    let io = first_io..engine.io.len();
    if io.len() != 1 {
        return Err(fail(
            ErrorClass::Infrastructure,
            UartPhase::FinalFootprint,
            "UART returning path must contain exactly one declared I/O event",
            rule,
            Some(view.instructions()[rule.words.start]),
        ));
    }
    let effect = engine.io[first_io].word;
    let depth = frame.covered_prefix_depth.ok_or_else(|| {
        fail(
            ErrorClass::Unsupported,
            UartPhase::FinalFootprint,
            "UART local depth is not established",
            rule,
            None,
        )
    })?;
    row(
        &mut engine.budget,
        UartPhase::FinalFootprint,
        rule,
        Some(view.instructions()[effect]),
        None,
    )?;
    Ok(UartLeaf {
        primitive: rule.primitive,
        operation: rule.operation,
        contribution: rule.contribution,
        effect,
        return_word: evidence.word,
        depth,
        memory: frame.memory_indices.clone(),
        io,
    })
}

/// Checks only the held UART contribution subset. Matching source names do not
/// establish the source-to-object producer chain, byte provenance, or handler calls.
pub fn inspect_uart_leaves_v3<'a>(
    bundle: &'a Bundle,
    text: TextInspection<'a>,
) -> std::result::Result<UartLeafInspection<'a>, UartInspectionError> {
    let emission = bundle
        .uart_leaf_identity_v3()
        .map_err(UartInspectionError::Projection)?;
    let machine = inspect_uart_machine_v3(text, emission).map_err(UartInspectionError::Machine)?;
    let view = machine.inventory();
    let mut budget = Budget {
        states: 0,
        facts: 0,
        peak_facts: 0,
        evaluations: 0,
        rows: view.witness_rows(),
    };
    let mut rules = bind(&view, machine.emission().primitives(), &mut budget)?;
    let mut engine = Engine::new(view, budget)?;
    // No unsupported body-shape result may hide a forbidden effect in a joined body.
    for rule in &mut rules {
        forbidden(&view, &engine.graph, rule, &mut engine.budget)?;
    }
    for rule in &rules {
        shape(&view, &engine.graph, rule, &mut engine.budget)?;
    }
    let mut leaves = Vec::with_capacity(rules.len());
    for rule in &rules {
        let first_io = engine.io.len();
        engine.worklist(rule.contribution, Policy::UartLeaf(rule))?;
        engine.finish(rule.contribution, Policy::UartLeaf(rule))?;
        leaves.push(completed(&mut engine, rule, first_io)?);
    }
    let data = engine.into_data()?;
    Ok(UartLeafInspection {
        machine,
        data,
        leaves,
    })
}
