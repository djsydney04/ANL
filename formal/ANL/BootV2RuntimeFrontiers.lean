import ANL.BootV2RuntimeEffectProofs
import ANL.BootRuntimeFrontierProofs

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (Pending Episode Landmark Delivery ParkControl)

/-- Local caller facts; the actual row must be legacy, not just signature-compatible. -/
def LegacyPendingAt (p : Program) (s : State) (q : Pending) : Prop :=
  q.origin = s.origins.control ∧ q.origin.function = s.machine.current.function ∧ 0 < q.ordinal ∧
  q.operation.Valid p.entries.hardware.function ∧ q.arguments.map Val.type = q.operation.params ∧
  match s.machine.control, p.functions[q.declaration]?, Origin.lookup p q.origin with
  | .invoke ident none values, some (.primitive row), some (.call ty target terms) =>
      ident = q.declaration ∧ target = q.declaration ∧ row.operation = .legacy q.operation ∧
      ty = q.operation.result ∧ terms.length = q.arguments.length ∧ values.reverse = q.arguments
  | _, _, _ => False

instance : Decidable (LegacyPendingAt p s q) := by
  unfold LegacyPendingAt
  split <;> infer_instance

inductive CapturedLegacy (p : Program) (s : State) : Pending → Prop where
  | invoke : s.machine.control = .invoke ident none values →
      p.functions[ident]? = some (.primitive row) → row.operation = .legacy operation →
      LegacyPendingAt p s ⟨s.nextOrdinal, ident, operation, values.reverse, s.origins.control⟩ →
      CapturedLegacy p s ⟨s.nextOrdinal, ident, operation, values.reverse, s.origins.control⟩

def captureLegacy (p : Program) (s : State) : Option Pending :=
  match s.machine.control with
  | .invoke ident none values => match p.functions[ident]? with
    | some (.primitive row) => match row.operation with
      | .legacy operation =>
        let q : Pending := ⟨s.nextOrdinal, ident, operation, values.reverse, s.origins.control⟩
        if LegacyPendingAt p s q then some q else none
      | .illegalInstruction _ => none
    | _ => none
  | _ => none

def LegacyBeforeValid (p : Program) (s : State) (q : Pending) : Prop :=
  LegacyPendingAt p s q ∧ q.ordinal = s.nextOrdinal
instance : Decidable (LegacyBeforeValid p s q) := inferInstanceAs (Decidable (_ ∧ _))

def LegacyAfterValid (p : Program) (s : State) (q : Pending) (value : Val) : Prop :=
  LegacyPendingAt p s q ∧ q.ordinal + 1 = s.nextOrdinal ∧ value.type = q.operation.result
instance : Decidable (LegacyAfterValid p s q value) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Phase-free facts. Installation, hardware validity and counters are deliberately absent. -/
def FaultAt (p : Program) (env : Environment) (s : State) (q : Fault.Request) : Prop :=
  s.episode = .boot ∧ s.machine.current.function = p.entries.boot.function ∧
  q.origin.function = p.entries.boot.function ∧ s.origins.control = q.origin ∧
  env.fault.illegalSitePc = some q.pc ∧
  match s.machine.control, p.operationAt q.declaration, Origin.lookup p q.origin with
  | .invoke ident none [], some (.illegalInstruction authority), some (.call ty target []) =>
      ident = q.declaration ∧ authority = 0 ∧ ty = unitTy ∧ target = q.declaration
  | _, _, _ => False

instance : Decidable (FaultAt p env s q) := by
  unfold FaultAt
  split <;> infer_instance

def checkFaultAt (p : Program) (env : Environment) (s : State) (q : Fault.Request) : Bool :=
  decide (FaultAt p env s q)

/-- Ready/Cut must separately require faultBefore; this guard does not test installation. -/
def FaultBeforeValid (p : Program) (env : Environment) (s : State) (q : Fault.Request) : Prop :=
  FaultAt p env s q ∧ 0 < q.ordinal ∧ q.ordinal = s.nextOrdinal ∧ s.forwardingUsed = false
instance : Decidable (FaultBeforeValid p env s q) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def checkFaultBefore (p : Program) (env : Environment) (s : State) (q : Fault.Request) : Bool :=
  decide (FaultBeforeValid p env s q)

/-- Execute must separately require faultCommit. Whole input validity stays at admission. -/
def FaultCommitValid (p : Program) (env : Environment) (s : State) (q : Fault.Request) : Prop :=
  FaultBeforeValid p env s q ∧ s.hardware.Valid ∧
    s.hardware.installedHandler = some p.entries.hardware.function
instance : Decidable (FaultCommitValid p env s q) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def checkFaultCommit (p : Program) (env : Environment) (s : State) (q : Fault.Request) : Bool :=
  decide (FaultCommitValid p env s q)

def LatestRaised (s : State) (q : Fault.Request) : Prop :=
  match s.revEvents with
  | .fault (.raised actual) :: _ => actual = q
  | _ => False
instance : Decidable (LatestRaised s q) := by
  unfold LatestRaised
  split <;> infer_instance

/-- Ready/Execute must separately require faultPending; the counter is post-raise. -/
def FaultRaisedValid (p : Program) (env : Environment) (s : State) (q : Fault.Request) : Prop :=
  FaultAt p env s q ∧ 0 < q.ordinal ∧ q.ordinal + 1 = s.nextOrdinal ∧
    s.forwardingUsed = false ∧ s.hardware.Valid ∧
    s.hardware.installedHandler = some p.entries.hardware.function ∧ LatestRaised s q
instance : Decidable (FaultRaisedValid p env s q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def checkFaultRaised (p : Program) (env : Environment) (s : State) (q : Fault.Request) : Bool :=
  decide (FaultRaisedValid p env s q)

inductive CapturedFault (p : Program) (env : Environment) (s : State) : Fault.Request → Prop where
  | invoke : s.machine.control = .invoke ident none values →
      p.operationAt ident = some (.illegalInstruction authority) → env.fault.illegalSitePc = some pc →
      FaultBeforeValid p env s ⟨s.nextOrdinal, ident, s.origins.control, pc⟩ →
      CapturedFault p env s ⟨s.nextOrdinal, ident, s.origins.control, pc⟩

def captureFault (p : Program) (env : Environment) (s : State) : Option Fault.Request :=
  match s.machine.control with
  | .invoke ident none _values => match p.operationAt ident with
    | some (.illegalInstruction _authority) => match env.fault.illegalSitePc with
      | some pc =>
        let q : Fault.Request := ⟨s.nextOrdinal, ident, s.origins.control, pc⟩
        if FaultBeforeValid p env s q then some q else none
      | none => none
    | _ => none
  | _ => none

def episodeFunction (p : Program) : Episode → Nat
  | .boot => p.entries.boot.function
  | .hardwareHandler => p.entries.hardware.function
  | .languageHandler => p.entries.language.function

inductive SelectedPark (p : Program) (episode : Episode) : ANL.Boot.Origin.Location → Prop where
  | role : p.functions[episodeFunction p episode]? = some (.defined d) →
      SelectedTail d.function.body path →
      SelectedPark p episode ⟨episodeFunction p episode, ANL.Boot.Origin.tailPath path⟩

def selectedLocation (p : Program) (episode : Episode) : Option ANL.Boot.Origin.Location := do
  match p.functions[episodeFunction p episode]? with
  | some (.defined d) =>
    let path ← designatedTail d.function.body
    return ⟨episodeFunction p episode, ANL.Boot.Origin.tailPath path⟩
  | _ => none

theorem selectedLocation_iff : selectedLocation p episode = some location ↔ SelectedPark p episode location := by
  constructor
  · intro found
    unfold selectedLocation at found
    cases row : p.functions[episodeFunction p episode]? with
    | none => simp [row] at found
    | some declaration =>
      cases declaration with
      | primitive _ => simp [row] at found
      | defined d =>
        simp only [row, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
        rcases found with ⟨path, tail, rfl⟩
        exact .role row (designatedTail_iff.mp tail)
  · intro meaning
    cases meaning with | role row tail => simp [selectedLocation, row, tail.search]

instance : Decidable (SelectedPark p episode location) :=
  decidable_of_iff (selectedLocation p episode = some location) selectedLocation_iff

def ParkAt (p : Program) (s : State) (location : ANL.Boot.Origin.Location) : Prop :=
  location = s.origins.control ∧ location.function = s.machine.current.function ∧
    SelectedPark p s.episode location ∧ ParkControl s.machine.control
instance : Decidable (ParkAt p s location) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def FirstPark (p : Program) (s : State) : Prop :=
  ParkAt p s s.origins.control ∧ s.episodeParkSeen = false ∧
    (s.episode = .boot → s.bootParkSeen = false)
instance : Decidable (FirstPark p s) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def ParkWaiting (p : Program) (s : State) (location : ANL.Boot.Origin.Location) : Prop :=
  ParkAt p s location ∧ s.episodeParkSeen = false ∧ (s.episode = .boot → s.bootParkSeen = false)
instance : Decidable (ParkWaiting p s location) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def ParkConsumed (p : Program) (s : State) (location : ANL.Boot.Origin.Location) : Prop :=
  ParkAt p s location ∧ s.episodeParkSeen = true ∧ (s.episode = .boot → s.bootParkSeen = true)
instance : Decidable (ParkConsumed p s location) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Eligible (p : Program) (s : State) : Prop :=
  s.episode = .boot ∧ s.hardware.installedHandler = some p.entries.hardware.function
instance : Decidable (Eligible p s) := inferInstanceAs (Decidable (_ ∧ _))

def deliveryAt (env : Environment) (s : State) (key : Landmark) : Option Delivery :=
  if s.deliveryUsed then none else
  match env.legacy.delivery with
  | some d => if d.landmark = key then some d else none
  | none => none

inductive DeliveryAt (env : Environment) (s : State) (key : Landmark) : Delivery → Prop where
  | matchKey : s.deliveryUsed = false → env.legacy.delivery = some d → d.landmark = key →
      DeliveryAt env s key d

def withPhase (s : State) (phase : Phase) : State := { s with phase := phase }

/-- A later finish rule must require LegacyAfterValid before using this raw update. -/
def returnLegacyState (s : State) (value : Val) : State :=
  { s with machine := { s.machine with control := .ret value }, phase := .legacy .ordinary }

def observedPark (s : State) (location : ANL.Boot.Origin.Location) : State :=
  { s with
    phase := .legacy (.parkObserved location), episodeParkSeen := true,
    bootParkSeen := if s.episode = .boot then true else s.bootParkSeen }

def ordinaryState (s : State) (machine : Words.State) (origins : ANL.Boot.Origin.Metadata) : State :=
  { s with machine := machine, origins := origins }

end ANL.Boot.V2.Runtime
