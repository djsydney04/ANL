import ANL.BootV2RuntimeCommands

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (wordValue WordAt noAllocations)

def raiseFaultState (s : State) (q : Fault.Request) : State :=
  { s with
    phase := .faultPending q
    nextOrdinal := s.nextOrdinal + 1
    revEvents := .fault (.raised q) :: s.revEvents }

inductive Raised (p : Program) (env : Environment) (s : State) (q : Fault.Request) : State → Prop where
  | raise : s.phase = .faultCommit q → FaultCommitValid p env s q →
      Raised p env s q (raiseFaultState s q)

def raiseFault (p : Program) (env : Environment) (s : State) (q : Fault.Request) : Option State :=
  if s.phase = .faultCommit q ∧ FaultCommitValid p env s q then some (raiseFaultState s q) else none

def ForwardBlocked (p : Program) (env : Environment) (s : State) (q : Fault.Request) : Prop :=
  s.phase = .faultPending q ∧ FaultRaisedValid p env s q ∧ env.fault.forwarding = none
instance : Decidable (ForwardBlocked p env s q) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The saved state is the actual faultPending caller, with no resumed-PC edge. -/
def forwardResetState (p : Program) (s : State) (q : Fault.Request) (machine : Words.State) : State :=
  { s with
    machine := machine
    origins := ANL.Boot.Origin.rootMetadata p.entries.hardware.function
    phase := .legacy .ordinary
    hardware := { s.hardware with sstatus := Fault.forwardedStatus s.hardware.sstatus }
    episode := .hardwareHandler
    stackRole := .terminal
    revEvents := .fault (.forwarded q) :: s.revEvents
    forwardingUsed := true
    episodeParkSeen := false
    interrupted := some s.snapshot }

inductive ForwardReset (p : Program) (env : Environment) (s : State) (q : Fault.Request) : State → Prop where
  | handler : s.phase = .faultPending q → FaultRaisedValid p env s q →
      env.fault.forwarding = some .forward →
      WordAt .w64 2 cause → WordAt .w64 q.pc pc → WordAt .w64 0 auxiliary →
      Enter p p.entries.hardware.function [cause, pc, auxiliary] s.machine.world machine →
      ForwardReset p env s q (forwardResetState p s q machine)

/-- Raw lookup checks row kind and payload bounds; checked typing is a separate theorem. -/
def resetForward (p : Program) (env : Environment) (s : State) (q : Fault.Request) : Option State := do
  if s.phase = .faultPending q ∧ FaultRaisedValid p env s q ∧ env.fault.forwarding = some .forward then
    let cause ← wordValue .w64 2
    let pc ← wordValue .w64 q.pc
    let auxiliary ← wordValue .w64 0
    let machine ← enter p p.entries.hardware.function [cause, pc, auxiliary] s.machine.world
    return forwardResetState p s q machine
  else none

inductive Execute (p : Program) (env : Environment) (s : State) : Command → TickResult → Prop where
  | language : LanguageReset p s tag next → Execute p env s (.language tag) (.advance next)
  | languageInvalid : (∀ next, ¬ LanguageReset p s tag next) → Execute p env s (.language tag) (.invalidState s)
  | enterPark : Execute p env s (.enterPark location) (.advance (withPhase s (.legacy (.parkCheck location))))
  | capturedLegacy : Execute p env s (.capturedLegacy q) (.advance (withPhase s (.legacy (.primitiveBefore q))))
  | capturedFault : Execute p env s (.capturedFault q) (.advance (withPhase s (.faultBefore q)))
  | ordinary : Origin.Step p noAllocations s.machine s.origins next origins →
      Execute p env s .ordinary (.advance (ordinaryState s next origins))
  | ordinaryInvalid : (∀ next origins, ¬ Origin.Step p noAllocations s.machine s.origins next origins) →
      Execute p env s .ordinary (.invalidState s)
  | legacyBefore : Cut p env s (.beforePrimitive q.ordinal q.declaration)
      (withPhase s (.legacy (.primitiveCommit q))) result → Execute p env s (.legacyBefore q) result
  | legacyCommit : LegacyEffect p env s.hardware s.readCursor q.operation q.arguments result →
      Execute p env s (.legacyCommit q) (.advance (commitLegacyState s q result))
  | blockedRead : LegacyReadBlocked p env s.hardware s.readCursor q.operation q.arguments →
      Execute p env s (.legacyCommit q) (.blockedRead s)
  | legacyInvalid : (∀ result, ¬ LegacyEffect p env s.hardware s.readCursor q.operation q.arguments result) →
      ¬ LegacyReadBlocked p env s.hardware s.readCursor q.operation q.arguments →
      Execute p env s (.legacyCommit q) (.invalidState s)
  | legacyAfter : Cut p env s (.afterPrimitive q.ordinal q.declaration)
      (withPhase s (.legacy (.primitiveReturn q value))) result → Execute p env s (.legacyAfter q value) result
  | legacyFinish : Execute p env s (.legacyFinish q value) (.advance (returnLegacyState s value))
  | parkBoot : s.episode = .boot → Cut p env s (.bootPark location) (observedPark s location) result →
      Execute p env s (.parkCheck location) result
  | parkHandler : s.episode ≠ .boot → Execute p env s (.parkCheck location) (.advance (observedPark s location))
  | parkResume : Execute p env s (.parkResume location) (.advance (withPhase s (.legacy .ordinary)))
  | faultBefore : Cut p env s (.beforePrimitive q.ordinal q.declaration)
      (withPhase s (.faultCommit q)) result → Execute p env s (.faultBefore q) result
  | raised : Raised p env s q next → Execute p env s (.faultCommit q) (.advance next)
  | raiseInvalid : (∀ next, ¬ Raised p env s q next) → Execute p env s (.faultCommit q) (.invalidState s)
  | forwardBlocked : ForwardBlocked p env s q → Execute p env s (.faultPending q) (.blockedForwarding s)
  | forwarded : ForwardReset p env s q next → Execute p env s (.faultPending q) (.advance next)
  | forwardInvalid : ¬ ForwardBlocked p env s q → (∀ next, ¬ ForwardReset p env s q next) →
      Execute p env s (.faultPending q) (.invalidState s)

def execute (p : Program) (env : Environment) (s : State) : Command → TickResult
  | .language tag => match resetLanguage p s tag with | some next => .advance next | none => .invalidState s
  | .enterPark location => .advance (withPhase s (.legacy (.parkCheck location)))
  | .capturedLegacy q => .advance (withPhase s (.legacy (.primitiveBefore q)))
  | .capturedFault q => .advance (withPhase s (.faultBefore q))
  | .ordinary => match Origin.step p noAllocations s.machine s.origins with
    | some (next, origins) => .advance (ordinaryState s next origins)
    | none => .invalidState s
  | .legacyBefore q => atCut p env s (.beforePrimitive q.ordinal q.declaration)
      (withPhase s (.legacy (.primitiveCommit q)))
  | .legacyCommit q => match performLegacy p env s.hardware s.readCursor q.operation q.arguments with
    | some result => .advance (commitLegacyState s q result)
    | none => if LegacyReadBlocked p env s.hardware s.readCursor q.operation q.arguments then .blockedRead s else .invalidState s
  | .legacyAfter q value => atCut p env s (.afterPrimitive q.ordinal q.declaration)
      (withPhase s (.legacy (.primitiveReturn q value)))
  | .legacyFinish _ value => .advance (returnLegacyState s value)
  | .parkCheck location =>
    if s.episode = .boot then atCut p env s (.bootPark location) (observedPark s location)
    else .advance (observedPark s location)
  | .parkResume _ => .advance (withPhase s (.legacy .ordinary))
  | .faultBefore q => atCut p env s (.beforePrimitive q.ordinal q.declaration) (withPhase s (.faultCommit q))
  | .faultCommit q => match raiseFault p env s q with | some next => .advance next | none => .invalidState s
  | .faultPending q =>
    if ForwardBlocked p env s q then .blockedForwarding s
    else match resetForward p env s q with | some next => .advance next | none => .invalidState s

inductive BootOutcome (p : Program) (env : Environment) (s : State) : TickResult → Prop where
  | ready : Ready p env s cmd → Execute p env s cmd result → BootOutcome p env s result
  | invalid : (∀ cmd, ¬ Ready p env s cmd) → BootOutcome p env s (.invalidState s)

inductive BootStep (p : Program) (env : Environment) : State → State → Prop where
  | advance : Ready p env s cmd → Execute p env s cmd (.advance next) → BootStep p env s next

/-- Admission owns the input scan; transitions never export or traverse the event prefix. -/
def tickRaw (p : Program) (env : Environment) (s : State) : TickResult :=
  match command p env s with | some cmd => execute p env s cmd | none => .invalidState s

def tick (p : Program) (input : ValidatedInput p) (s : State) : TickResult := tickRaw p input.raw s

end ANL.Boot.V2.Runtime
