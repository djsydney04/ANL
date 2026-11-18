import ANL.BootRuntimeEffectProofs

namespace ANL.Boot.Runtime
open ANL.Words

/-- Local captured-call checks; these deliberately do not certify every saved origin frame. -/
def PendingAt (p : Program) (s : State) (q : Pending) : Prop :=
  q.origin = s.origins.control ∧ q.origin.function = s.machine.current.function ∧ 0 < q.ordinal ∧
  q.operation.Valid p.entries.hardware.function ∧ q.arguments.map Val.type = q.operation.params ∧
  match s.machine.control, p.functions[q.declaration]?, Origin.lookup p q.origin with
  | .invoke ident none values, some (.primitive row), some (.call ty target terms) =>
      ident = q.declaration ∧ target = q.declaration ∧ row.operation = q.operation ∧
      ty = q.operation.result ∧ terms.length = q.arguments.length ∧ values.reverse = q.arguments
  | _, _, _ => False

instance : Decidable (PendingAt p s q) := by
  unfold PendingAt
  split <;> infer_instance

inductive Captured (p : Program) (s : State) : Pending → Prop where
  | invoke : s.machine.control = .invoke ident none values →
      p.functions[ident]? = some (.primitive row) →
      PendingAt p s ⟨s.nextOrdinal, ident, row.operation, values.reverse, s.origins.control⟩ →
      Captured p s ⟨s.nextOrdinal, ident, row.operation, values.reverse, s.origins.control⟩

def capture (p : Program) (s : State) : Option Pending :=
  match s.machine.control with
  | .invoke ident none values =>
    match p.functions[ident]? with
    | some (.primitive row) =>
      let q : Pending := ⟨s.nextOrdinal, ident, row.operation, values.reverse, s.origins.control⟩
      if PendingAt p s q then some q else none
    | _ => none
  | _ => none

def Episode.function (p : Program) : Episode → Nat
  | .boot => p.entries.boot.function
  | .hardwareHandler => p.entries.hardware.function
  | .languageHandler => p.entries.language.function

inductive SelectedPark (p : Program) (episode : Episode) : Origin.Location → Prop where
  | role : p.functions[episode.function p]? = some (.defined d) →
      SelectedTail d.function.body path →
      SelectedPark p episode ⟨episode.function p, Origin.tailPath path⟩

def selectedLocation (p : Program) (episode : Episode) : Option Origin.Location := do
  match p.functions[episode.function p]? with
  | some (.defined d) =>
    let path ← designatedTail d.function.body
    return ⟨episode.function p, Origin.tailPath path⟩
  | _ => none

 theorem selectedLocation_iff : selectedLocation p episode = some location ↔ SelectedPark p episode location := by
  constructor
  · intro found
    unfold selectedLocation at found
    cases row : p.functions[episode.function p]? with
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

/-- Equality to the exact literal-true empty loop, with an executable specialized decision. -/
def ParkControl : Control → Prop
  | .eval term => term = park
  | _ => False

instance {ctl : Control} : Decidable (ParkControl ctl) := by
  cases ctl <;> try exact isFalse (by intro h; exact h)
  exact decidable_of_iff (isPark _ = true) isPark_iff

def ParkAt (p : Program) (s : State) (location : Origin.Location) : Prop :=
  location = s.origins.control ∧ location.function = s.machine.current.function ∧
  SelectedPark p s.episode location ∧ ParkControl s.machine.control
instance : Decidable (ParkAt p s location) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The boot landmark is single-use independently of handler-episode park observations. -/
def FirstPark (p : Program) (s : State) : Prop :=
  ParkAt p s s.origins.control ∧ s.episodeParkSeen = false ∧
    (s.episode = .boot → s.bootParkSeen = false)
instance : Decidable (FirstPark p s) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Eligible (p : Program) (s : State) : Prop :=
  s.episode = .boot ∧ s.hardware.installedHandler = some p.entries.hardware.function
instance : Decidable (Eligible p s) := inferInstanceAs (Decidable (_ ∧ _))

/-- Matching a key does not itself authorize delivery or assert that it will ever be reached. -/
def deliveryAt (env : Environment) (s : State) (key : Landmark) : Option Delivery :=
  if s.deliveryUsed then none else
  match env.delivery with
  | some d => if d.landmark = key then some d else none
  | none => none

inductive DeliveryAt (env : Environment) (s : State) (key : Landmark) : Delivery → Prop where
  | matchKey : s.deliveryUsed = false → env.delivery = some d → d.landmark = key → DeliveryAt env s key d

/-- Pure administrative phase changes retain every other raw field. -/
def withPhase (s : State) (phase : Phase) : State := { s with phase := phase }

def returnState (s : State) (value : Val) : State :=
  { s with machine := { s.machine with control := .ret value }, phase := .ordinary }

def observedPark (s : State) (location : Origin.Location) : State :=
  { s with
    phase := .parkObserved location, episodeParkSeen := true,
    bootParkSeen := if s.episode = .boot then true else s.bootParkSeen }

def ordinaryState (s : State) (machine : Words.State) (origins : Origin.Metadata) : State :=
  { s with machine := machine, origins := origins }

/-- Fixed irrelevant response source; admitted boot controls never allocate. -/
def noAllocations : ANL.Memory.Responses := fun _ => .refused

end ANL.Boot.Runtime
