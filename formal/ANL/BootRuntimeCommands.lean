import ANL.BootRuntimeFrontierProofs

namespace ANL.Boot.Runtime
open ANL.Words

/-- A local dispatch decision, not a future scheduler or a proof-carrying state. -/
inductive Command where
  | language (tag : Nat)
  | enterPark (location : Origin.Location)
  | captured (pending : Pending)
  | ordinary
  | before (pending : Pending)
  | commit (pending : Pending)
  | after (pending : Pending) (value : Val)
  | finish (pending : Pending) (value : Val)
  | parkCheck (location : Origin.Location)
  | parkResume (location : Origin.Location)
  deriving DecidableEq, Repr

def NonTrap : Control → Prop
  | .trap _ => False
  | _ => True
instance {ctl : Control} : Decidable (NonTrap ctl) := by cases ctl <;> unfold NonTrap <;> infer_instance

def BeforeValid (p : Program) (s : State) (q : Pending) : Prop :=
  PendingAt p s q ∧ q.ordinal = s.nextOrdinal
instance : Decidable (BeforeValid p s q) := inferInstanceAs (Decidable (_ ∧ _))
def AfterValid (p : Program) (s : State) (q : Pending) (v : Val) : Prop :=
  PendingAt p s q ∧ q.ordinal + 1 = s.nextOrdinal ∧ v.type = q.operation.result
instance : Decidable (AfterValid p s q v) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def ParkWaiting (p : Program) (s : State) (location : Origin.Location) : Prop :=
  ParkAt p s location ∧ s.episodeParkSeen = false ∧ (s.episode = .boot → s.bootParkSeen = false)
instance : Decidable (ParkWaiting p s location) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def ParkConsumed (p : Program) (s : State) (location : Origin.Location) : Prop :=
  ParkAt p s location ∧ s.episodeParkSeen = true ∧ (s.episode = .boot → s.bootParkSeen = true)
instance : Decidable (ParkConsumed p s location) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Independent priority rules over actual controls and local phase frontiers. -/
inductive Ready (p : Program) (s : State) : Command → Prop where
  | language : s.phase = .ordinary → s.machine.control = .trap trap → LanguageTag trap tag → Ready p s (.language tag)
  | park : s.phase = .ordinary → FirstPark p s → Ready p s (.enterPark s.origins.control)
  | capture : s.phase = .ordinary → ¬ FirstPark p s → Captured p s q → Ready p s (.captured q)
  | ordinary : s.phase = .ordinary → NonTrap s.machine.control → ¬ FirstPark p s →
      (∀ q, ¬ Captured p s q) → Ready p s .ordinary
  | before : s.phase = .primitiveBefore q → BeforeValid p s q → Ready p s (.before q)
  | commit : s.phase = .primitiveCommit q → BeforeValid p s q → Ready p s (.commit q)
  | after : s.phase = .primitiveAfter q v → AfterValid p s q v → Ready p s (.after q v)
  | finish : s.phase = .primitiveReturn q v → AfterValid p s q v → Ready p s (.finish q v)
  | parkCheck : s.phase = .parkCheck location → ParkWaiting p s location → Ready p s (.parkCheck location)
  | parkResume : s.phase = .parkObserved location → ParkConsumed p s location → Ready p s (.parkResume location)

def command (p : Program) (s : State) : Option Command :=
  match s.phase with
  | .ordinary =>
    match s.machine.control with
    | .trap trap => (languageTag trap).map Command.language
    | _ =>
      if FirstPark p s then some (.enterPark s.origins.control)
      else match capture p s with | some q => some (.captured q) | none => some .ordinary
  | .primitiveBefore q => if BeforeValid p s q then some (.before q) else none
  | .primitiveCommit q => if BeforeValid p s q then some (.commit q) else none
  | .primitiveAfter q v => if AfterValid p s q v then some (.after q v) else none
  | .primitiveReturn q v => if AfterValid p s q v then some (.finish q v) else none
  | .parkCheck location => if ParkWaiting p s location then some (.parkCheck location) else none
  | .parkObserved location => if ParkConsumed p s location then some (.parkResume location) else none

end ANL.Boot.Runtime
