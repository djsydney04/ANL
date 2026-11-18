import ANL.BootRuntimeCommands

namespace ANL.Boot.Runtime
open ANL.Words

/-- Independent rules for a reached delivery cutpoint. Eligibility is checked before reset. -/
inductive Cut (p : Program) (env : Environment) (s : State) (key : Landmark) (fallback : State) : TickResult → Prop where
  | absent : (∀ d, ¬ DeliveryAt env s key d) → Cut p env s key fallback (.advance fallback)
  | ineligible : DeliveryAt env s key d → ¬ Eligible p s → Cut p env s key fallback (.ineligibleDelivery s)
  | deliver : DeliveryAt env s key d → Eligible p s → HardwareReset p s d next →
      Cut p env s key fallback (.advance next)
  | invalid : DeliveryAt env s key d → Eligible p s → (∀ next, ¬ HardwareReset p s d next) →
      Cut p env s key fallback (.invalidState s)

def atCut (p : Program) (env : Environment) (s : State) (key : Landmark) (fallback : State) : TickResult :=
  match deliveryAt env s key with
  | none => .advance fallback
  | some d =>
    if Eligible p s then
      match resetHardware p s d with | some next => .advance next | none => .invalidState s
    else .ineligibleDelivery s

/-- Independent effects/reset/ordinary rules after local dispatch. -/
inductive Execute (p : Program) (env : Environment) (s : State) : Command → TickResult → Prop where
  | language : LanguageReset p s tag next → Execute p env s (.language tag) (.advance next)
  | languageInvalid : (∀ next, ¬ LanguageReset p s tag next) → Execute p env s (.language tag) (.invalidState s)
  | enterPark : Execute p env s (.enterPark location) (.advance (withPhase s (.parkCheck location)))
  | captured : Execute p env s (.captured q) (.advance (withPhase s (.primitiveBefore q)))
  | ordinary : Origin.Step p noAllocations s.machine s.origins next origins →
      Execute p env s .ordinary (.advance (ordinaryState s next origins))
  | ordinaryInvalid : (∀ next origins, ¬ Origin.Step p noAllocations s.machine s.origins next origins) →
      Execute p env s .ordinary (.invalidState s)
  | before : Cut p env s (.beforePrimitive q.ordinal q.declaration) (withPhase s (.primitiveCommit q)) result →
      Execute p env s (.before q) result
  | commit : Effect p env s.hardware s.readCursor q.operation q.arguments result →
      Execute p env s (.commit q) (.advance (commitState s q result))
  | blocked : ReadBlocked p env s.hardware s.readCursor q.operation q.arguments →
      Execute p env s (.commit q) (.blockedRead s)
  | commitInvalid : (∀ result, ¬ Effect p env s.hardware s.readCursor q.operation q.arguments result) →
      ¬ ReadBlocked p env s.hardware s.readCursor q.operation q.arguments →
      Execute p env s (.commit q) (.invalidState s)
  | after : Cut p env s (.afterPrimitive q.ordinal q.declaration) (withPhase s (.primitiveReturn q v)) result →
      Execute p env s (.after q v) result
  | finish : Execute p env s (.finish q v) (.advance (returnState s v))
  | parkBoot : s.episode = .boot →
      Cut p env s (.bootPark location) (observedPark s location) result →
      Execute p env s (.parkCheck location) result
  | parkHandler : s.episode ≠ .boot →
      Execute p env s (.parkCheck location) (.advance (observedPark s location))
  | parkResume : Execute p env s (.parkResume location) (.advance (withPhase s .ordinary))

/-- Internal operation on arbitrary raw input; callers normally use the validated gateway tick. -/
def execute (p : Program) (env : Environment) (s : State) : Command → TickResult
  | .language tag => match resetLanguage p s tag with | some next => .advance next | none => .invalidState s
  | .enterPark location => .advance (withPhase s (.parkCheck location))
  | .captured q => .advance (withPhase s (.primitiveBefore q))
  | .ordinary =>
    match Origin.step p noAllocations s.machine s.origins with
    | some (next, origins) => .advance (ordinaryState s next origins)
    | none => .invalidState s
  | .before q => atCut p env s (.beforePrimitive q.ordinal q.declaration) (withPhase s (.primitiveCommit q))
  | .commit q =>
    match perform p env s.hardware s.readCursor q.operation q.arguments with
    | some result => .advance (commitState s q result)
    | none => if ReadBlocked p env s.hardware s.readCursor q.operation q.arguments then .blockedRead s else .invalidState s
  | .after q v => atCut p env s (.afterPrimitive q.ordinal q.declaration) (withPhase s (.primitiveReturn q v))
  | .finish _ v => .advance (returnState s v)
  | .parkCheck location =>
    if s.episode = .boot then atCut p env s (.bootPark location) (observedPark s location)
    else .advance (observedPark s location)
  | .parkResume _ => .advance (withPhase s .ordinary)

inductive BootOutcome (p : Program) (env : Environment) (s : State) : TickResult → Prop where
  | ready : Ready p s cmd → Execute p env s cmd result → BootOutcome p env s result
  | invalid : (∀ cmd, ¬ Ready p s cmd) → BootOutcome p env s (.invalidState s)

inductive BootStep (p : Program) (env : Environment) : State → State → Prop where
  | advance : Ready p s cmd → Execute p env s cmd (.advance next) → BootStep p env s next

/-- No finite-read scan, delivery-scope scan, trace export, or allocation occurs at this gateway. -/
def tickRaw (p : Program) (env : Environment) (s : State) : TickResult :=
  match command p s with | some cmd => execute p env s cmd | none => .invalidState s

def tick (p : Program) (input : ValidatedInput p) (s : State) : TickResult := tickRaw p input.raw s

end ANL.Boot.Runtime
