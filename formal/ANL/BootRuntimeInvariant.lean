import ANL.BootRuntimeTick

namespace ANL.Boot.Runtime
open ANL.Words

/-- Pure ordinary frames can retain values but never buffer resources or loans. -/
def FrameClean : Frame → Prop
  | .heapLength .. | .heapInitial .. | .owner .. | .readIndex .. | .writeIndex .. | .writeValue .. => False
  | .callReturn caller loan => caller.resources = [] ∧ loan = none
  | _ => True

def MemoryFreeState (machine : Words.State) : Prop :=
  machine.world = .initial ∧ machine.current.resources = [] ∧ ∀ frame ∈ machine.kont, FrameClean frame

/-- The episode belongs to the outer role activation; a helper's current function is different. -/
inductive EpisodeChain : Nat → List Frame → Nat → Prop where
  | nil : EpisodeChain role [] role
  | caller : EpisodeChain caller.function rest role → EpisodeChain current (.callReturn caller loan :: rest) role
  | frame : (∀ caller loan, frame ≠ .callReturn caller loan) →
      EpisodeChain current rest role → EpisodeChain current (frame :: rest) role

inductive EpisodeStack : Episode → StackRole → Prop where
  | boot : EpisodeStack .boot .boot
  | hardware : EpisodeStack .hardwareHandler .terminal
  | language : EpisodeStack .languageHandler .terminal

/-- A pending result agrees with the just-recorded transaction, without describing device internals. -/
inductive PayloadValue (q : Pending) : Payload → Val → Prop where
  | read : q.operation = .read8 region offset → WordAt .w8 n v → PayloadValue q (.read n) v
  | write : q.operation = .write8 region offset → q.arguments = [operand] → WordAt .w8 n operand →
      PayloadValue q (.write n) unitValue
  | fence : q.operation = .fence region → PayloadValue q .unit unitValue
  | clear : q.operation = .csrClear authority register mask → PayloadValue q .unit unitValue
  | set : q.operation = .csrWrite authority register n → PayloadValue q .unit unitValue
  | install : q.operation = .installTrap authority target → PayloadValue q .unit unitValue

def LatestCommit (s : State) (q : Pending) (v : Val) : Prop :=
  ∃ payload rest, s.revEvents = .primitive q.ordinal q.declaration q.operation payload :: rest ∧ PayloadValue q payload v

/-- This describes concrete local state, not tick's output or membership in a future execution. -/
inductive PhaseInvariant (p : Program) (s : State) : Prop where
  | ordinary : s.phase = .ordinary → PhaseInvariant p s
  | before : s.phase = .primitiveBefore q → BeforeValid p s q → PhaseInvariant p s
  | commit : s.phase = .primitiveCommit q → BeforeValid p s q → PhaseInvariant p s
  | after : s.phase = .primitiveAfter q v → AfterValid p s q v → LatestCommit s q v → PhaseInvariant p s
  | finish : s.phase = .primitiveReturn q v → AfterValid p s q v → LatestCommit s q v → PhaseInvariant p s
  | parkWaiting : s.phase = .parkCheck location → ParkWaiting p s location → PhaseInvariant p s
  | parkConsumed : s.phase = .parkObserved location → ParkConsumed p s location → PhaseInvariant p s

structure SnapshotInvariant (p : Program) (snapshot : Interrupted) : Prop where
  typed : Words.State.Typed p.carrier snapshot.machine unitTy
  aligned : Origin.Aligned p snapshot.machine snapshot.origins
  memory : MemoryFreeState snapshot.machine
  stack : EpisodeStack snapshot.episode snapshot.stackRole
  episode : EpisodeChain snapshot.machine.current.function snapshot.machine.kont (snapshot.episode.function p)

/-- Local candidate for the next preservation checkpoint. A complete event History is deliberately separate. -/
structure RuntimeInvariant (p : Program) (env : Environment) (s : State) : Prop where
  typed : Words.State.Typed p.carrier s.machine unitTy
  aligned : Origin.Aligned p s.machine s.origins
  memory : MemoryFreeState s.machine
  hardware : s.hardware.Valid
  installed : s.hardware.installedHandler = none ∨ s.hardware.installedHandler = some p.entries.hardware.function
  stack : EpisodeStack s.episode s.stackRole
  episode : EpisodeChain s.machine.current.function s.machine.kont (s.episode.function p)
  phase : PhaseInvariant p s
  cursor : s.readCursor ≤ env.reads.length
  ordinal : 0 < s.nextOrdinal
  bootSeen : s.episode = .boot → s.episodeParkSeen = true → s.bootParkSeen = true
  passive : ∀ snapshot, s.interrupted = some snapshot → SnapshotInvariant p snapshot

end ANL.Boot.Runtime
