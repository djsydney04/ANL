//! Entry-relative facts stop at unresolved effects and interfunction transfers.
use crate::machine::MachineInspection;
use crate::machine::decode::{Decoded, Effect, Op, Operands};
use crate::machine::machine::{ContributionId, Instruction, WordId};
use crate::machine::text::MAX_WITNESS_ROWS;
use crate::machine::text::elf::ErrorClass;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

mod setup;
pub use setup::{
    CallUse, ConditionalSetupStackBounds, IdentityJoin, ReturningSetupLeaf, RootEntry,
    SetupStackInspection, StackError, inspect_setup_stacks,
};

pub const MAX_STATES: usize = 100_000;
pub const MAX_FACTS: usize = 1_000_000;
pub const MAX_TRANSFERS: usize = 1_000_000;
pub const CALLEE_SAVED: u32 = (1 << 8) | (1 << 9) | (0x3ff << 18);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage {
    Index,
    Worklist,
    FinalGraph,
    SetupBind,
    SetupLeaf,
    SetupResume,
    SetupRoot,
}
#[derive(Debug)]
pub struct FrameError {
    pub class: ErrorClass,
    pub stage: Stage,
    pub reason: &'static str,
    pub contribution: Option<ContributionId>,
    pub word: Option<WordId>,
}
type Result<T> = std::result::Result<T, FrameError>;
fn error(class: ErrorClass, stage: Stage, reason: &'static str) -> FrameError {
    FrameError {
        class,
        stage,
        reason,
        contribution: None,
        word: None,
    }
}
fn invariant(stage: Stage, reason: &'static str) -> FrameError {
    error(ErrorClass::Infrastructure, stage, reason)
}
#[derive(Clone, Copy)]
struct Site {
    contribution: ContributionId,
    word: WordId,
}
impl Site {
    fn of(instruction: Instruction) -> Self {
        Self {
            contribution: instruction.contribution,
            word: instruction.id,
        }
    }
}
fn located(mut e: FrameError, site: Site) -> FrameError {
    e.contribution = Some(site.contribution);
    e.word = Some(site.word);
    e
}
fn index_error(reason: &'static str, words: &[Instruction], word: WordId) -> FrameError {
    let mut e = invariant(Stage::Index, reason);
    e.word = Some(word);
    e.contribution = words.get(word).map(|w| w.contribution);
    e
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fact {
    Unknown,
    Const(u64),
    EntryRegister(u8),
    EntrySpPlus(i64),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Slot {
    pub offset: i64,
    pub width: u8,
}
pub struct State {
    registers: [Fact; 32],
    slots: BTreeMap<Slot, Fact>,
}
impl State {
    pub fn registers(&self) -> &[Fact; 32] {
        &self.registers
    }
    pub fn slots(&self) -> impl Iterator<Item = (&Slot, &Fact)> {
        self.slots.iter()
    }
    fn fact_count(&self) -> usize {
        32 + self.slots.len()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Access {
    Load,
    Store,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemoryGap {
    NonFrameAddress,
    UnknownSp,
    OutsideFrame,
    Misaligned,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrontierKind {
    Transfer {
        transfer_index: usize,
        target: WordId,
        link_register: u8,
        continuation: Option<WordId>,
        link_value: Option<u64>,
    },
    SpOutsideDomain {
        value: Fact,
    },
    Memory {
        access: Access,
        address: Fact,
        width: u8,
        sp: Fact,
        gap: MemoryGap,
    },
    Csr,
    Fence,
    ReturnNotEstablished,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Frontier {
    pub word: WordId,
    pub kind: FrontierKind,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryObservation {
    pub word: WordId,
    pub access: Access,
    pub offset: i64,
    pub width: u8,
    pub value: Fact,
    pub discarded_load: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReturnEvidence {
    pub word: WordId,
    pub sp: Fact,
    pub ra: Fact,
    pub restored_registers: u32,
    pub established: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Coverage {
    ClosedLocalReturns,
    ClosedLocalNoReturnSites,
    Partial,
}
pub struct LocalReturnSummary {
    contribution: ContributionId,
    local_depth_bound: u64,
    returns: Range<usize>,
}
impl LocalReturnSummary {
    pub fn contribution(&self) -> ContributionId {
        self.contribution
    }
    pub fn local_depth_bound(&self) -> u64 {
        self.local_depth_bound
    }
    pub fn return_indices(&self) -> Range<usize> {
        self.returns.clone()
    }
}
pub struct ContributionFrames {
    pub contribution: ContributionId,
    pub coverage: Coverage,
    pub covered_words: usize,
    pub covered_prefix_depth: Option<u64>,
    pub frontier_indices: Range<usize>,
    pub memory_indices: Range<usize>,
    pub return_indices: Range<usize>,
    summary: Option<LocalReturnSummary>,
}
impl ContributionFrames {
    pub fn local_return_summary(&self) -> Option<&LocalReturnSummary> {
        self.summary.as_ref()
    }
    pub fn local_depth_bound(&self) -> Option<u64> {
        if self.coverage == Coverage::Partial {
            None
        } else {
            self.covered_prefix_depth
        }
    }
}
#[derive(Clone, Copy, Debug)]
pub struct Counters {
    pub created_states: usize,
    pub retained_states: usize,
    pub peak_facts: usize,
    pub retained_facts: usize,
    pub transfer_evaluations: usize,
    pub charged_rows: usize,
}
/// Private construction retains its exact machine and conditional premises.
pub struct LocalFrameInspection<'a> {
    machine: MachineInspection<'a>,
    data: FrameData,
}
impl<'a> LocalFrameInspection<'a> {
    pub fn machine(&self) -> &MachineInspection<'a> {
        &self.machine
    }
    pub fn state(&self, word: WordId) -> Option<&State> {
        self.data.states.get(word).and_then(Option::as_deref)
    }
    pub fn contributions(&self) -> &[ContributionFrames] {
        &self.data.contributions
    }
    pub fn frontiers(&self) -> &[Frontier] {
        &self.data.frontiers
    }
    pub fn memory(&self) -> &[MemoryObservation] {
        &self.data.memory
    }
    pub fn returns(&self) -> &[ReturnEvidence] {
        &self.data.returns
    }
    pub fn counters(&self) -> Counters {
        self.data.counters
    }
}

struct FrameData {
    states: Vec<Option<Box<State>>>,
    contributions: Vec<ContributionFrames>,
    frontiers: Vec<Frontier>,
    memory: Vec<MemoryObservation>,
    returns: Vec<ReturnEvidence>,
    counters: Counters,
    calls: Vec<setup::CallUse>,
}

struct Budget {
    states: usize,
    facts: usize,
    peak_facts: usize,
    evaluations: usize,
    rows: usize,
}
impl Budget {
    fn row(&mut self, stage: Stage) -> Result<()> {
        if self.rows >= MAX_WITNESS_ROWS {
            return Err(error(
                ErrorClass::Resource,
                stage,
                "combined frame witness limit exceeded",
            ));
        }
        self.rows += 1;
        Ok(())
    }
    fn facts(&mut self, count: usize, stage: Stage) -> Result<()> {
        let next = self
            .facts
            .checked_add(count)
            .filter(|n| *n <= MAX_FACTS)
            .ok_or_else(|| {
                error(
                    ErrorClass::Resource,
                    stage,
                    "live frame fact limit exceeded",
                )
            })?;
        self.facts = next;
        self.peak_facts = self.peak_facts.max(next);
        Ok(())
    }
    fn release(&mut self, count: usize, stage: Stage) -> Result<()> {
        self.facts = self
            .facts
            .checked_sub(count)
            .ok_or_else(|| invariant(stage, "frame fact accounting underflow"))?;
        Ok(())
    }
    fn state(&mut self, stage: Stage) -> Result<()> {
        if self.states >= MAX_STATES {
            return Err(error(
                ErrorClass::Resource,
                stage,
                "frame state limit exceeded",
            ));
        }
        self.row(stage)?;
        self.states += 1;
        Ok(())
    }
    fn evaluation(&mut self, stage: Stage) -> Result<()> {
        if self.evaluations >= MAX_TRANSFERS {
            return Err(error(
                ErrorClass::Resource,
                stage,
                "frame transfer limit exceeded",
            ));
        }
        self.evaluations += 1;
        Ok(())
    }
}
fn copied(state: &State, budget: &mut Budget, stage: Stage) -> Result<State> {
    budget.facts(state.fact_count(), stage)?;
    Ok(State {
        registers: state.registers,
        slots: state.slots.clone(),
    })
}
fn entry(budget: &mut Budget) -> Result<State> {
    budget.facts(32, Stage::Worklist)?;
    let mut registers = std::array::from_fn(|r| Fact::EntryRegister(r as u8));
    registers[0] = Fact::Const(0);
    registers[2] = Fact::EntrySpPlus(0);
    Ok(State {
        registers,
        slots: BTreeMap::new(),
    })
}
fn join(target: &mut State, incoming: &State, budget: &mut Budget) -> Result<bool> {
    let mut changed = false;
    for (old, new) in target.registers.iter_mut().zip(incoming.registers) {
        if *old != new && *old != Fact::Unknown {
            *old = Fact::Unknown;
            changed = true;
        }
    }
    let before = target.slots.len();
    target
        .slots
        .retain(|slot, value| incoming.slots.get(slot) == Some(value));
    let removed = before - target.slots.len();
    budget.release(removed, Stage::Worklist)?;
    Ok(changed || removed != 0)
}
fn included(specific: &State, general: &State) -> bool {
    specific
        .registers
        .iter()
        .zip(general.registers)
        .all(|(a, b)| b == Fact::Unknown || *a == b)
        && general
            .slots
            .iter()
            .all(|(s, v)| specific.slots.get(s) == Some(v))
}

#[derive(Clone, Copy, Default)]
struct Links {
    local: [Option<WordId>; 2],
    transfer: Option<usize>,
    continuation: Option<WordId>,
    returns: bool,
}
struct Graph {
    links: Vec<Links>,
    entries: Vec<WordId>,
}
fn graph(machine: &MachineInspection<'_>) -> Result<Graph> {
    let words = machine.instructions();
    let count = words.len();
    let contributions = machine.text().contributions().len();
    if count > MAX_WITNESS_ROWS || contributions > MAX_WITNESS_ROWS {
        return Err(error(
            ErrorClass::Resource,
            Stage::Index,
            "frame index limit exceeded",
        ));
    }
    let mut links = vec![Links::default(); count];
    let mut starts = vec![None; contributions];
    for (id, word) in words.iter().enumerate() {
        if word.id != id || word.contribution >= contributions {
            return Err(located(
                invariant(Stage::Index, "machine instruction identity changed"),
                Site {
                    contribution: word.contribution,
                    word: id,
                },
            ));
        }
        starts[word.contribution].get_or_insert(id);
    }
    for edge in machine.local_edges() {
        if edge.source >= count
            || edge.target >= count
            || words[edge.source].contribution != words[edge.target].contribution
        {
            return Err(index_error(
                "machine local edge changed",
                words,
                edge.source,
            ));
        }
        let row = &mut links[edge.source].local;
        let slot = row
            .iter_mut()
            .find(|x| x.is_none())
            .ok_or_else(|| index_error("machine local fanout changed", words, edge.source))?;
        *slot = Some(edge.target);
    }
    for (id, transfer) in machine.transfers().iter().enumerate() {
        let row = links.get_mut(transfer.source).ok_or_else(|| {
            index_error("machine transfer source changed", words, transfer.source)
        })?;
        if row.transfer.replace(id).is_some() {
            return Err(index_error(
                "duplicate machine transfer",
                words,
                transfer.source,
            ));
        }
    }
    for continuation in machine.continuations() {
        let row = links.get_mut(continuation.source).ok_or_else(|| {
            index_error(
                "machine continuation source changed",
                words,
                continuation.source,
            )
        })?;
        if row.continuation.replace(continuation.target).is_some() || row.transfer.is_none() {
            return Err(index_error(
                "machine continuation identity changed",
                words,
                continuation.source,
            ));
        }
    }
    for &word in machine.returns() {
        let row = links
            .get_mut(word)
            .ok_or_else(|| index_error("machine return source changed", words, word))?;
        if row.returns || row.transfer.is_some() {
            return Err(index_error(
                "machine return classification changed",
                words,
                word,
            ));
        }
        row.returns = true;
    }
    let mut entries = Vec::with_capacity(contributions);
    for (contribution, start) in starts.into_iter().enumerate() {
        entries.push(start.ok_or_else(|| {
            let mut e = invariant(Stage::Index, "empty machine contribution");
            e.contribution = Some(contribution);
            e
        })?);
    }
    Ok(Graph { links, entries })
}
fn queued(queue: &mut BTreeSet<WordId>, word: WordId, stage: Stage) -> Result<()> {
    if !queue.contains(&word) && queue.len() >= MAX_STATES {
        return Err(error(
            ErrorClass::Resource,
            stage,
            "frame queue limit exceeded",
        ));
    }
    queue.insert(word);
    Ok(())
}

fn add_immediate(value: Fact, immediate: i64) -> Fact {
    match value {
        Fact::Const(x) => Fact::Const(x.wrapping_add(immediate as u64)),
        Fact::EntrySpPlus(x) => x
            .checked_add(immediate)
            .map(Fact::EntrySpPlus)
            .unwrap_or(Fact::Unknown),
        value if immediate == 0 => value,
        _ => Fact::Unknown,
    }
}
fn value(instruction: Instruction, state: &State) -> Option<(u8, Fact)> {
    use Op::*;
    let decoded = instruction.ordinary()?;
    let registers = &state.registers;
    let result = match decoded.operands {
        Operands::Upper { rd, immediate } => {
            let result = match decoded.operation {
                Lui => Fact::Const(immediate as u64),
                Auipc => Fact::Const(instruction.pc.wrapping_add(immediate as u64)),
                _ => Fact::Unknown,
            };
            (rd, result)
        }
        Operands::Immediate { rd, rs1, immediate } => {
            let source = registers[usize::from(rs1)];
            let result = match (decoded.operation, source) {
                (Addi, x) => add_immediate(x, immediate),
                (Andi, Fact::Const(x)) => Fact::Const(x & immediate as u64),
                _ => Fact::Unknown,
            };
            (rd, result)
        }
        Operands::Registers { rd, rs1, rs2 } => {
            let a = registers[usize::from(rs1)];
            let b = registers[usize::from(rs2)];
            let result = match (decoded.operation, a, b) {
                (Or, x, Fact::Const(0)) | (Or, Fact::Const(0), x) => x,
                (Add, Fact::Const(x), Fact::Const(y)) => Fact::Const(x.wrapping_add(y)),
                (Sub, Fact::Const(x), Fact::Const(y)) => Fact::Const(x.wrapping_sub(y)),
                (And, Fact::Const(x), Fact::Const(y)) => Fact::Const(x & y),
                (Or, Fact::Const(x), Fact::Const(y)) => Fact::Const(x | y),
                (Xor, Fact::Const(x), Fact::Const(y)) => Fact::Const(x ^ y),
                _ => Fact::Unknown,
            };
            (rd, result)
        }
        _ => return None,
    };
    Some(result)
}
fn low(value: u64, width: u8) -> u64 {
    if width == 8 {
        value
    } else {
        value & ((1_u64 << (width * 8)) - 1)
    }
}
fn stored(value: Fact, width: u8) -> Fact {
    match value {
        Fact::Const(x) => Fact::Const(low(x, width)),
        x if width == 8 => x,
        _ => Fact::Unknown,
    }
}
fn loaded(value: Fact, width: u8, signed: bool) -> Fact {
    match value {
        Fact::Const(x) => {
            let x = low(x, width);
            let result = if signed && width < 8 {
                let shift = 64 - width * 8;
                (((x << shift) as i64) >> shift) as u64
            } else {
                x
            };
            Fact::Const(result)
        }
        x if width == 8 => x,
        _ => Fact::Unknown,
    }
}
fn slot_end(slot: Slot) -> i128 {
    i128::from(slot.offset) + i128::from(slot.width)
}
fn memory_slot(state: &State, address: Fact, width: u8) -> std::result::Result<Slot, MemoryGap> {
    let Fact::EntrySpPlus(offset) = address else {
        return Err(MemoryGap::NonFrameAddress);
    };
    let Fact::EntrySpPlus(sp) = state.registers[2] else {
        return Err(MemoryGap::UnknownSp);
    };
    if offset.rem_euclid(i64::from(width)) != 0 {
        return Err(MemoryGap::Misaligned);
    }
    let slot = Slot { offset, width };
    if offset < sp || slot_end(slot) > 0 {
        return Err(MemoryGap::OutsideFrame);
    }
    Ok(slot)
}
fn write_slot(
    state: &mut State,
    slot: Slot,
    value: Fact,
    budget: &mut Budget,
    stage: Stage,
) -> Result<()> {
    let before = state.slots.len();
    state.slots.retain(|old, _| {
        slot_end(*old) <= i128::from(slot.offset) || slot_end(slot) <= i128::from(old.offset)
    });
    budget.release(before - state.slots.len(), stage)?;
    if value != Fact::Unknown {
        budget.facts(1, stage)?;
        state.slots.insert(slot, value);
    }
    Ok(())
}
fn return_evidence(word: WordId, state: &State) -> ReturnEvidence {
    let mut mask = 0;
    for r in 0_u8..32 {
        if CALLEE_SAVED & (1_u32 << r) != 0
            && state.registers[usize::from(r)] == Fact::EntryRegister(r)
        {
            mask |= 1_u32 << r;
        }
    }
    let sp = state.registers[2];
    let ra = state.registers[1];
    ReturnEvidence {
        word,
        sp,
        ra,
        restored_registers: mask,
        established: sp == Fact::EntrySpPlus(0)
            && ra == Fact::EntryRegister(1)
            && mask == CALLEE_SAVED,
    }
}
// Keep the fixed 32-register result inline; copied() charges its temporary facts
// before construction. Boxing would add an allocation to every supported transfer.
#[derive(Clone, Copy)]
enum Policy<'p> {
    Local,
    Leaf(&'p setup::LeafRule),
    Role(&'p [setup::ReturningSetupLeaf]),
}
#[allow(clippy::large_enum_variant)]
enum Step {
    Continue(
        State,
        Option<MemoryObservation>,
        [Option<WordId>; 2],
        Option<setup::CallUse>,
    ),
    Frontier(FrontierKind, Option<MemoryObservation>),
    Return(ReturnEvidence),
}
fn step(
    machine: &MachineInspection<'_>,
    graph: &Graph,
    instruction: Instruction,
    state: &State,
    budget: &mut Budget,
    stage: Stage,
    policy: Policy<'_>,
) -> Result<Step> {
    budget.evaluation(stage)?;
    let decoded = ordinary(instruction, stage)?;
    let links = graph.links[instruction.id];
    if let Some(id) = links.transfer {
        if let Policy::Role(leaves) = policy
            && let Some(resumed) =
                setup::resume(machine, graph, instruction, state, budget, stage, leaves)?
        {
            return Ok(resumed);
        }
        let transfer = machine.transfers()[id];
        let link_value = if transfer.link_register == 0 {
            None
        } else {
            Some(
                instruction
                    .pc
                    .checked_add(4)
                    .ok_or_else(|| invariant(stage, "machine link PC changed"))?,
            )
        };
        return Ok(Step::Frontier(
            FrontierKind::Transfer {
                transfer_index: id,
                target: transfer.target,
                link_register: transfer.link_register,
                continuation: links.continuation,
                link_value,
            },
            None,
        ));
    }
    if links.returns {
        let mut evidence = return_evidence(instruction.id, state);
        if matches!(policy, Policy::Role(_)) {
            // A root begins with arbitrary RA, never an ordinary aligned return premise.
            evidence.established = false;
        }
        return Ok(Step::Return(evidence));
    }
    match decoded.effect {
        Effect::Csr { .. } => {
            if let Policy::Leaf(rule) = policy {
                setup::authorize_csr(instruction, state, rule)?;
                return Ok(Step::Continue(
                    copied(state, budget, stage)?,
                    None,
                    links.local,
                    None,
                ));
            }
            return Ok(Step::Frontier(FrontierKind::Csr, None));
        }
        Effect::Fence => return Ok(Step::Frontier(FrontierKind::Fence, None)),
        _ => {}
    }
    let mut memory = None;
    let mut memory_change = None;
    let mut destination = value(instruction, state);
    match decoded.effect {
        Effect::Load { bytes, .. } | Effect::Store { bytes } => {
            if !matches!(bytes, 1 | 2 | 4 | 8) {
                return Err(invariant(stage, "machine memory width changed"));
            }
            let (access, base, offset, register) = match decoded.operands {
                Operands::Load { rd, base, offset } => (Access::Load, base, offset, rd),
                Operands::Store {
                    source,
                    base,
                    offset,
                } => (Access::Store, base, offset, source),
                _ => return Err(invariant(stage, "machine memory operands changed")),
            };
            let address = add_immediate(state.registers[usize::from(base)], offset);
            let slot = match memory_slot(state, address, bytes) {
                Ok(slot) => slot,
                Err(gap) => {
                    return Ok(Step::Frontier(
                        FrontierKind::Memory {
                            access,
                            address,
                            width: bytes,
                            sp: state.registers[2],
                            gap,
                        },
                        None,
                    ));
                }
            };
            let observed = match access {
                Access::Load => {
                    let signed = match decoded.effect {
                        Effect::Load { sign_extend, .. } => sign_extend,
                        _ => return Err(invariant(stage, "machine load effect changed")),
                    };
                    let result = loaded(
                        state.slots.get(&slot).copied().unwrap_or(Fact::Unknown),
                        bytes,
                        signed,
                    );
                    destination = Some((register, result));
                    result
                }
                Access::Store => {
                    let result = stored(state.registers[usize::from(register)], bytes);
                    memory_change = Some((slot, result));
                    result
                }
            };
            memory = Some(MemoryObservation {
                word: instruction.id,
                access,
                offset: slot.offset,
                width: bytes,
                value: observed,
                discarded_load: access == Access::Load && register == 0,
            });
        }
        _ => {}
    }
    if let Some((2, fact)) = destination
        && !matches!(fact, Fact::EntrySpPlus(offset) if offset <= 0 && offset % 16 == 0)
    {
        return Ok(Step::Frontier(
            FrontierKind::SpOutsideDomain { value: fact },
            memory,
        ));
    }
    let mut output = copied(state, budget, stage)?;
    if let Some((slot, fact)) = memory_change {
        write_slot(&mut output, slot, fact, budget, stage)?;
    }
    if let Some((register, fact)) = destination {
        if register != 0 {
            output.registers[usize::from(register)] = fact;
        }
        if register == 2 {
            let Fact::EntrySpPlus(sp) = fact else {
                return Err(invariant(stage, "SP admission changed"));
            };
            let before = output.slots.len();
            output
                .slots
                .retain(|slot, _| slot.offset >= sp && slot_end(*slot) <= 0);
            budget.release(before - output.slots.len(), stage)?;
        }
    }
    Ok(Step::Continue(output, memory, links.local, None))
}

struct Engine<'m, 'a> {
    machine: &'m MachineInspection<'a>,
    graph: Graph,
    budget: Budget,
    states: Vec<Option<Box<State>>>,
    visited: Vec<bool>,
    contributions: Vec<ContributionFrames>,
    frontiers: Vec<Frontier>,
    memory: Vec<MemoryObservation>,
    returns: Vec<ReturnEvidence>,
    calls: Vec<setup::CallUse>,
}
impl<'m, 'a> Engine<'m, 'a> {
    fn new(machine: &'m MachineInspection<'a>, budget: Budget) -> Result<Self> {
        let graph = graph(machine)?;
        let n = machine.instructions().len();
        let mut budget = budget;
        for &root in &graph.entries {
            budget
                .row(Stage::Index)
                .map_err(|e| located(e, Site::of(machine.instructions()[root])))?;
        }
        let count = graph.entries.len();
        Ok(Self {
            machine,
            graph,
            budget,
            states: (0..n).map(|_| None).collect(),
            visited: vec![false; n],
            contributions: Vec::with_capacity(count),
            frontiers: Vec::new(),
            memory: Vec::new(),
            returns: Vec::new(),
            calls: Vec::new(),
        })
    }
    fn worklist(&mut self, contribution: ContributionId, policy: Policy<'_>) -> Result<()> {
        let Self {
            machine,
            graph,
            budget,
            states,
            ..
        } = self;
        let root = graph.entries[contribution];
        let root_site = Site::of(machine.instructions()[root]);
        budget
            .state(Stage::Worklist)
            .map_err(|e| located(e, root_site))?;
        states[root] = Some(Box::new(entry(budget).map_err(|e| located(e, root_site))?));
        let mut queue = BTreeSet::new();
        queued(&mut queue, root, Stage::Worklist).map_err(|e| located(e, root_site))?;
        while let Some(word) = queue.pop_first() {
            let instruction = machine.instructions()[word];
            let site = Site::of(instruction);
            let state = states[word].as_deref().ok_or_else(|| {
                located(
                    invariant(Stage::Worklist, "missing queued frame state"),
                    site,
                )
            })?;
            let result = step(
                machine,
                graph,
                instruction,
                state,
                budget,
                Stage::Worklist,
                policy,
            )
            .map_err(|e| located(e, site))?;
            if let Step::Continue(output, _, successors, _) = result {
                for target in successors.into_iter().flatten() {
                    let target_site = Site::of(machine.instructions()[target]);
                    let changed = if let Some(target_state) = states[target].as_deref_mut() {
                        join(target_state, &output, budget).map_err(|e| located(e, target_site))?
                    } else {
                        budget
                            .state(Stage::Worklist)
                            .map_err(|e| located(e, target_site))?;
                        states[target] = Some(Box::new(
                            copied(&output, budget, Stage::Worklist)
                                .map_err(|e| located(e, target_site))?,
                        ));
                        true
                    };
                    if changed {
                        queued(&mut queue, target, Stage::Worklist)
                            .map_err(|e| located(e, target_site))?;
                    }
                }
                budget
                    .release(output.fact_count(), Stage::Worklist)
                    .map_err(|e| located(e, site))?;
            }
        }

        Ok(())
    }
    fn finish(&mut self, contribution: ContributionId, policy: Policy<'_>) -> Result<()> {
        let Self {
            machine,
            graph,
            budget,
            states,
            visited,
            contributions,
            frontiers,
            memory,
            returns,
            calls,
        } = self;
        let root = graph.entries[contribution];
        let first_frontier = frontiers.len();
        let first_memory = memory.len();
        let first_return = returns.len();
        let mut covered_words = 0;
        let mut depth = Some(0_u64);
        let mut queue = BTreeSet::new();
        let root_site = Site::of(machine.instructions()[root]);
        queued(&mut queue, root, Stage::FinalGraph).map_err(|e| located(e, root_site))?;
        while let Some(word) = queue.pop_first() {
            if visited[word] {
                continue;
            }
            visited[word] = true;
            let site = Site::of(machine.instructions()[word]);
            covered_words += 1;
            let state = states[word].as_deref().ok_or_else(|| {
                located(
                    invariant(Stage::FinalGraph, "missing final frame state"),
                    site,
                )
            })?;
            depth = match (depth, state.registers[2]) {
                (Some(old), Fact::EntrySpPlus(offset)) if offset <= 0 => {
                    Some(old.max((-i128::from(offset)) as u64))
                }
                _ => None,
            };
            let result = step(
                machine,
                graph,
                machine.instructions()[word],
                state,
                budget,
                Stage::FinalGraph,
                policy,
            )
            .map_err(|e| located(e, site))?;
            let observation = match result {
                Step::Continue(output, observation, successors, call) => {
                    if let Some(call) = call {
                        budget
                            .row(Stage::SetupResume)
                            .map_err(|e| located(e, site))?;
                        calls.push(call);
                    }
                    for target in successors.into_iter().flatten() {
                        let target_site = Site::of(machine.instructions()[target]);
                        let target_state = states[target].as_deref().ok_or_else(|| {
                            located(
                                invariant(Stage::FinalGraph, "missing final successor state"),
                                target_site,
                            )
                        })?;
                        if !included(&output, target_state) {
                            return Err(located(
                                invariant(Stage::FinalGraph, "final frame edge is not closed"),
                                site,
                            ));
                        }
                        if !visited[target] {
                            queued(&mut queue, target, Stage::FinalGraph)
                                .map_err(|e| located(e, target_site))?;
                        }
                    }
                    budget
                        .release(output.fact_count(), Stage::FinalGraph)
                        .map_err(|e| located(e, site))?;
                    observation
                }
                Step::Frontier(kind, observation) => {
                    budget
                        .row(Stage::FinalGraph)
                        .map_err(|e| located(e, site))?;
                    frontiers.push(Frontier { word, kind });
                    observation
                }
                Step::Return(evidence) => {
                    budget
                        .row(Stage::FinalGraph)
                        .map_err(|e| located(e, site))?;
                    returns.push(evidence);
                    if !evidence.established {
                        budget
                            .row(Stage::FinalGraph)
                            .map_err(|e| located(e, site))?;
                        frontiers.push(Frontier {
                            word,
                            kind: FrontierKind::ReturnNotEstablished,
                        });
                    }
                    None
                }
            };
            if let Some(observation) = observation {
                budget
                    .row(Stage::FinalGraph)
                    .map_err(|e| located(e, site))?;
                memory.push(observation);
            }
        }
        let return_range = first_return..returns.len();
        let closed = first_frontier == frontiers.len() && depth.is_some();
        let coverage = if !closed {
            Coverage::Partial
        } else if return_range.is_empty() {
            Coverage::ClosedLocalNoReturnSites
        } else {
            Coverage::ClosedLocalReturns
        };
        let summary = if coverage == Coverage::ClosedLocalReturns {
            Some(LocalReturnSummary {
                contribution,
                local_depth_bound: depth.ok_or_else(|| {
                    located(
                        invariant(Stage::FinalGraph, "closed depth changed"),
                        root_site,
                    )
                })?,
                returns: return_range.clone(),
            })
        } else {
            None
        };
        contributions.push(ContributionFrames {
            contribution,
            coverage,
            covered_words,
            covered_prefix_depth: depth,
            frontier_indices: first_frontier..frontiers.len(),
            memory_indices: first_memory..memory.len(),
            return_indices: return_range,
            summary,
        });

        Ok(())
    }
    fn into_data(self) -> Result<FrameData> {
        let Self {
            machine,
            mut budget,
            mut states,
            visited,
            contributions,
            frontiers,
            memory,
            returns,
            calls,
            ..
        } = self;
        let mut retained_states = 0;
        for (word, cell) in states.iter_mut().enumerate() {
            if visited[word] {
                retained_states += 1;
            } else if let Some(old) = cell.take() {
                budget
                    .release(old.fact_count(), Stage::FinalGraph)
                    .map_err(|e| located(e, Site::of(machine.instructions()[word])))?;
            }
        }
        let counters = Counters {
            created_states: budget.states,
            retained_states,
            peak_facts: budget.peak_facts,
            retained_facts: budget.facts,
            transfer_evaluations: budget.evaluations,
            charged_rows: budget.rows,
        };

        Ok(FrameData {
            states,
            contributions,
            frontiers,
            memory,
            returns,
            counters,
            calls,
        })
    }
}
fn budget(machine: &MachineInspection<'_>) -> Budget {
    Budget {
        states: 0,
        facts: 0,
        peak_facts: 0,
        evaluations: 0,
        rows: machine.witness_rows(),
    }
}

fn ordinary(instruction: Instruction, stage: Stage) -> Result<Decoded> {
    instruction.ordinary().ok_or_else(|| {
        located(
            error(
                ErrorClass::Unsupported,
                stage,
                "architectural exception frames are not implemented by this entrypoint",
            ),
            Site::of(instruction),
        )
    })
}
fn require_ordinary(machine: &MachineInspection<'_>, stage: Stage) -> Result<()> {
    if let Some(site) = machine.illegal_site() {
        return Err(located(
            error(
                ErrorClass::Unsupported,
                stage,
                "architectural exception frames are not implemented by this entrypoint",
            ),
            Site::of(machine.instructions()[site.word()]),
        ));
    }
    Ok(())
}

pub fn inspect_local_frames<'a>(
    machine: MachineInspection<'a>,
) -> Result<LocalFrameInspection<'a>> {
    require_ordinary(&machine, Stage::Index)?;
    let mut engine = Engine::new(&machine, budget(&machine))?;
    // Preserve the accepted local scheduling and counter order exactly.
    for contribution in 0..engine.graph.entries.len() {
        engine.worklist(contribution, Policy::Local)?;
    }
    for contribution in 0..engine.graph.entries.len() {
        engine.finish(contribution, Policy::Local)?;
    }
    let data = engine.into_data()?;
    Ok(LocalFrameInspection { machine, data })
}
