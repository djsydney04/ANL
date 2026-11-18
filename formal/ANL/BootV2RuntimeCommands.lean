import ANL.BootV2RuntimeFrontierProofs

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (Pending Landmark LanguageTag languageTag NonTrap)

inductive TickResult where
  | advance (state : State)
  | blockedRead (state : State)
  | blockedForwarding (state : State)
  | ineligibleDelivery (state : State)
  | invalidState (state : State)
  deriving Repr

def TickResult.state : TickResult → State
  | .advance s | .blockedRead s | .blockedForwarding s | .ineligibleDelivery s | .invalidState s => s

inductive Command where
  | language (tag : Nat)
  | enterPark (location : ANL.Boot.Origin.Location)
  | capturedLegacy (pending : Pending)
  | capturedFault (request : Fault.Request)
  | ordinary
  | legacyBefore (pending : Pending)
  | legacyCommit (pending : Pending)
  | legacyAfter (pending : Pending) (value : Val)
  | legacyFinish (pending : Pending) (value : Val)
  | parkCheck (location : ANL.Boot.Origin.Location)
  | parkResume (location : ANL.Boot.Origin.Location)
  | faultBefore (request : Fault.Request)
  | faultCommit (request : Fault.Request)
  | faultPending (request : Fault.Request)
  deriving DecidableEq, Repr

/-- Phase checks authorize the phase-free local predicates at a dispatch boundary. -/
inductive Ready (p : Program) (env : Environment) (s : State) : Command → Prop where
  | language : s.phase = .legacy .ordinary → s.machine.control = .trap trap →
      LanguageTag trap tag → Ready p env s (.language tag)
  | park : s.phase = .legacy .ordinary → FirstPark p s → Ready p env s (.enterPark s.origins.control)
  | captureLegacy : s.phase = .legacy .ordinary → ¬ FirstPark p s →
      CapturedLegacy p s q → Ready p env s (.capturedLegacy q)
  | captureFault : s.phase = .legacy .ordinary → ¬ FirstPark p s →
      (∀ q, ¬ CapturedLegacy p s q) → CapturedFault p env s q → Ready p env s (.capturedFault q)
  | ordinary : s.phase = .legacy .ordinary → NonTrap s.machine.control → ¬ FirstPark p s →
      (∀ q, ¬ CapturedLegacy p s q) → (∀ q, ¬ CapturedFault p env s q) → Ready p env s .ordinary
  | legacyBefore : s.phase = .legacy (.primitiveBefore q) → LegacyBeforeValid p s q →
      Ready p env s (.legacyBefore q)
  | legacyCommit : s.phase = .legacy (.primitiveCommit q) → LegacyBeforeValid p s q →
      Ready p env s (.legacyCommit q)
  | legacyAfter : s.phase = .legacy (.primitiveAfter q value) → LegacyAfterValid p s q value →
      Ready p env s (.legacyAfter q value)
  | legacyFinish : s.phase = .legacy (.primitiveReturn q value) → LegacyAfterValid p s q value →
      Ready p env s (.legacyFinish q value)
  | parkCheck : s.phase = .legacy (.parkCheck location) → ParkWaiting p s location →
      Ready p env s (.parkCheck location)
  | parkResume : s.phase = .legacy (.parkObserved location) → ParkConsumed p s location →
      Ready p env s (.parkResume location)
  | faultBefore : s.phase = .faultBefore q → FaultBeforeValid p env s q → Ready p env s (.faultBefore q)
  | faultCommit : s.phase = .faultCommit q → FaultCommitValid p env s q → Ready p env s (.faultCommit q)
  | faultPending : s.phase = .faultPending q → FaultRaisedValid p env s q → Ready p env s (.faultPending q)

def command (p : Program) (env : Environment) (s : State) : Option Command :=
  match s.phase with
  | .legacy phase => match phase with
    | .ordinary => match s.machine.control with
      | .trap trap => (languageTag trap).map Command.language
      | _ =>
        if FirstPark p s then some (.enterPark s.origins.control)
        else match captureLegacy p s with
          | some q => some (.capturedLegacy q)
          | none => match captureFault p env s with
            | some q => some (.capturedFault q)
            | none => some .ordinary
    | .primitiveBefore q => if LegacyBeforeValid p s q then some (.legacyBefore q) else none
    | .primitiveCommit q => if LegacyBeforeValid p s q then some (.legacyCommit q) else none
    | .primitiveAfter q value => if LegacyAfterValid p s q value then some (.legacyAfter q value) else none
    | .primitiveReturn q value => if LegacyAfterValid p s q value then some (.legacyFinish q value) else none
    | .parkCheck location => if ParkWaiting p s location then some (.parkCheck location) else none
    | .parkObserved location => if ParkConsumed p s location then some (.parkResume location) else none
  | .faultBefore q => if FaultBeforeValid p env s q then some (.faultBefore q) else none
  | .faultCommit q => if FaultCommitValid p env s q then some (.faultCommit q) else none
  | .faultPending q => if FaultRaisedValid p env s q then some (.faultPending q) else none

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

end ANL.Boot.V2.Runtime
