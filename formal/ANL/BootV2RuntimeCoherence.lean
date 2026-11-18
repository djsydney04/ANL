import ANL.BootV2RuntimeFaultLaws
import ANL.BootRuntimeInvariant

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (Pending PayloadValue MemoryFreeState EpisodeStack EpisodeChain)
variable {p : ANL.Boot.V2.Program} {env : Environment} {s : State}
set_option linter.unusedSimpArgs false

/-- Only fields actually stored in Interrupted are inspected. -/
def SnapshotLegacyAt (p : Program) (z : Interrupted) (q : Pending) : Prop :=
  q.origin = z.origins.control ∧ q.origin.function = z.machine.current.function ∧ 0 < q.ordinal ∧
  q.operation.Valid p.entries.hardware.function ∧ q.arguments.map Val.type = q.operation.params ∧
  match z.machine.control, p.functions[q.declaration]?, Origin.lookup p q.origin with
  | .invoke ident none values, some (.primitive row), some (.call ty target terms) =>
      ident = q.declaration ∧ target = q.declaration ∧ row.operation = .legacy q.operation ∧
      ty = q.operation.result ∧ terms.length = q.arguments.length ∧ values.reverse = q.arguments
  | _, _, _ => False

def SnapshotFaultAt (p : Program) (env : Environment) (z : Interrupted) (q : Fault.Request) : Prop :=
  z.episode = .boot ∧ z.machine.current.function = p.entries.boot.function ∧
  q.origin.function = p.entries.boot.function ∧ z.origins.control = q.origin ∧
  env.fault.illegalSitePc = some q.pc ∧
  match z.machine.control, p.operationAt q.declaration, Origin.lookup p q.origin with
  | .invoke ident none [], some (.illegalInstruction authority), some (.call ty target []) =>
      ident = q.declaration ∧ authority = 0 ∧ ty = unitTy ∧ target = q.declaration
  | _, _, _ => False

def SnapshotParkAt (p : Program) (z : Interrupted) (location : ANL.Boot.Origin.Location) : Prop :=
  location = z.origins.control ∧ location.function = z.machine.current.function ∧
    SelectedPark p z.episode location ∧ ANL.Boot.Runtime.ParkControl z.machine.control

/-- No saved hardware, counter, flags or event list exists in this record. -/
inductive SnapshotPhaseShape (p : Program) (env : Environment) (z : Interrupted) : Prop where
  | ordinary : z.phase = .legacy .ordinary → SnapshotPhaseShape p env z
  | before : z.phase = .legacy (.primitiveBefore q) → SnapshotLegacyAt p z q → SnapshotPhaseShape p env z
  | commit : z.phase = .legacy (.primitiveCommit q) → SnapshotLegacyAt p z q → SnapshotPhaseShape p env z
  | after : z.phase = .legacy (.primitiveAfter q value) → SnapshotLegacyAt p z q →
      value.type = q.operation.result → SnapshotPhaseShape p env z
  | finish : z.phase = .legacy (.primitiveReturn q value) → SnapshotLegacyAt p z q →
      value.type = q.operation.result → SnapshotPhaseShape p env z
  | parkWaiting : z.phase = .legacy (.parkCheck location) → SnapshotParkAt p z location → SnapshotPhaseShape p env z
  | parkConsumed : z.phase = .legacy (.parkObserved location) → SnapshotParkAt p z location → SnapshotPhaseShape p env z
  | faultBefore : z.phase = .faultBefore q → SnapshotFaultAt p env z q → 0 < q.ordinal → SnapshotPhaseShape p env z
  | faultCommit : z.phase = .faultCommit q → SnapshotFaultAt p env z q → 0 < q.ordinal → SnapshotPhaseShape p env z
  | faultPending : z.phase = .faultPending q → SnapshotFaultAt p env z q → 0 < q.ordinal → SnapshotPhaseShape p env z

structure SnapshotCoherent (p : Program) (env : Environment) (z : Interrupted) : Prop where
  typed : Words.State.Typed p.carrier z.machine unitTy
  aligned : Origin.Aligned p z.machine z.origins
  memory : MemoryFreeState z.machine
  stack : EpisodeStack z.episode z.stackRole
  episode : EpisodeChain z.machine.current.function z.machine.kont (episodeFunction p z.episode)
  phase : SnapshotPhaseShape p env z

/-- A local head fact, without a history-prefix or provenance premise. -/
def LatestLegacyCommit (s : State) (q : Pending) (value : Val) : Prop :=
  ∃ payload rest, s.revEvents = .legacy (.primitive q.ordinal q.declaration q.operation payload) :: rest ∧
    PayloadValue q payload value

inductive PhaseCoherent (p : Program) (env : Environment) (s : State) : Prop where
  | ordinary : s.phase = .legacy .ordinary → PhaseCoherent p env s
  | before : s.phase = .legacy (.primitiveBefore q) → LegacyBeforeValid p s q → PhaseCoherent p env s
  | commit : s.phase = .legacy (.primitiveCommit q) → LegacyBeforeValid p s q → PhaseCoherent p env s
  | after : s.phase = .legacy (.primitiveAfter q value) → LegacyAfterValid p s q value →
      LatestLegacyCommit s q value → PhaseCoherent p env s
  | finish : s.phase = .legacy (.primitiveReturn q value) → LegacyAfterValid p s q value →
      LatestLegacyCommit s q value → PhaseCoherent p env s
  | parkWaiting : s.phase = .legacy (.parkCheck location) → ParkWaiting p s location → PhaseCoherent p env s
  | parkConsumed : s.phase = .legacy (.parkObserved location) → ParkConsumed p s location → PhaseCoherent p env s
  | faultBefore : s.phase = .faultBefore q → FaultBeforeValid p env s q → PhaseCoherent p env s
  /-- The no-D phase advance does not establish installation. -/
  | faultCommit : s.phase = .faultCommit q → FaultBeforeValid p env s q → PhaseCoherent p env s
  | faultPending : s.phase = .faultPending q → FaultRaisedValid p env s q → PhaseCoherent p env s

structure Coherent (p : Program) (env : Environment) (s : State) : Prop where
  typed : Words.State.Typed p.carrier s.machine unitTy
  aligned : Origin.Aligned p s.machine s.origins
  memory : MemoryFreeState s.machine
  hardware : s.hardware.Valid
  installed : s.hardware.installedHandler = none ∨ s.hardware.installedHandler = some p.entries.hardware.function
  stack : EpisodeStack s.episode s.stackRole
  episode : EpisodeChain s.machine.current.function s.machine.kont (episodeFunction p s.episode)
  phase : PhaseCoherent p env s
  cursor : s.readCursor ≤ env.legacy.reads.length
  ordinal : 0 < s.nextOrdinal
  bootSeen : s.episode = .boot → s.episodeParkSeen = true → s.bootParkSeen = true
  passive : ∀ snapshot, s.interrupted = some snapshot → SnapshotCoherent p env snapshot

theorem PhaseCoherent.snapshot (phase : PhaseCoherent p env s) : SnapshotPhaseShape p env s.snapshot := by
  cases phase with
  | ordinary eq => exact .ordinary eq
  | before eq valid => exact .before eq valid.1
  | commit eq valid => exact .commit eq valid.1
  | after eq valid _ => exact .after eq valid.1 valid.2.2
  | finish eq valid _ => exact .finish eq valid.1 valid.2.2
  | parkWaiting eq valid => exact .parkWaiting eq valid.1
  | parkConsumed eq valid => exact .parkConsumed eq valid.1
  | faultBefore eq valid => exact .faultBefore eq valid.1 valid.2.1
  | faultCommit eq valid => exact .faultCommit eq valid.1 valid.2.1
  | faultPending eq valid => exact .faultPending eq valid.1 valid.2.1

theorem Coherent.snapshot (old : Coherent p env s) : SnapshotCoherent p env s.snapshot :=
  ⟨old.typed, old.aligned, old.memory, old.stack, old.episode, old.phase.snapshot⟩

theorem PhaseCoherent.commit_before (coherent : PhaseCoherent p env s) (phase : s.phase = .faultCommit q) :
    FaultBeforeValid p env s q := by
  cases coherent <;> simp_all

theorem Coherent.faultCommit_ready_iff (old : Coherent p env s) (phase : s.phase = .faultCommit q) :
    Ready p env s (.faultCommit q) ↔ s.hardware.installedHandler = some p.entries.hardware.function := by
  constructor
  · intro ready
    cases ready with | faultCommit _ valid => exact valid.2.2
  · intro installed
    exact .faultCommit phase ⟨old.phase.commit_before phase, old.hardware, installed⟩

theorem Coherent.faultCommit_uninstalled_invalid (_old : Coherent p env s)
    (phase : s.phase = .faultCommit q) (uninstalled : s.hardware.installedHandler = none) :
    tickRaw p env s = .invalidState s := by
  have invalid : ¬ FaultCommitValid p env s q := by
    intro valid
    have bad := uninstalled.symm.trans valid.2.2
    cases bad
  simp [tickRaw, command, phase, invalid]

theorem PhaseCoherent.legacy_after_operation (coherent : PhaseCoherent p env s)
    (phase : s.phase = .legacy (.primitiveAfter q value)) :
    p.operationAt q.declaration = some (.legacy q.operation) := by
  have valid : LegacyAfterValid p s q value := by cases coherent <;> simp_all
  exact valid.1.operation

theorem PhaseCoherent.legacy_return_operation (coherent : PhaseCoherent p env s)
    (phase : s.phase = .legacy (.primitiveReturn q value)) :
    p.operationAt q.declaration = some (.legacy q.operation) := by
  have valid : LegacyAfterValid p s q value := by cases coherent <;> simp_all
  exact valid.1.operation

end ANL.Boot.V2.Runtime
