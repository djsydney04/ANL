import ANL.BootRuntimeReachableFacts
import ANL.BootRuntimeSelectedSpin

namespace ANL.Boot.Runtime
open ANL.Words

inductive ObservationKind where
  | handlerEntry (episode : Episode)
  | park (episode : Episode) (location : Origin.Location)
  deriving DecidableEq, Repr

/-- Recognition of the fixed authored handler body, not a history or reachability assertion. -/
def HandlerControl : Control → Prop
  | .eval term => term = handler
  | _ => False
instance {ctl : Control} : Decidable (HandlerControl ctl) := by
  cases ctl <;> try exact isFalse (by intro h; exact h)
  exact decidable_of_iff (isHandler _ = true) isHandler_iff

def HandlerDefinition (p : Program) (episode : Episode) : Prop :=
  match p.functions[episode.function p]? with
  | some (.defined d) => d.function.body = handler
  | _ => False
instance : Decidable (HandlerDefinition p episode) := by
  unfold HandlerDefinition
  split
  · exact decidable_of_iff (isHandler _ = true) isHandler_iff
  · exact isFalse (by intro h; exact h)

/-- Only local fields are inspected. A retained snapshot is not itself evidence of a past reset. -/
def FreshHandler (p : Program) (s : State) : Prop :=
  s.episode ≠ .boot ∧ HandlerDefinition p s.episode ∧
  s.phase = .ordinary ∧ HandlerControl s.machine.control ∧
  s.machine.current.function = s.episode.function p ∧ s.stackRole = .terminal ∧
  s.episodeParkSeen = false ∧
  match s.machine.kont, s.machine.current.resources, s.origins.frames, s.interrupted with
  | [], [], [], some _ => s.origins.control = Origin.Location.root (s.episode.function p)
  | _, _, _, _ => False
instance : Decidable (FreshHandler p s) := by
  unfold FreshHandler
  split <;> infer_instance

inductive Observation (p : Program) (s : State) : ObservationKind → Prop where
  | handler : FreshHandler p s → Observation p s (.handlerEntry s.episode)
  | park : s.phase = .parkObserved location → ParkConsumed p s location →
      Observation p s (.park s.episode location)

/-- State-only classifier: no transition, response lookup, reset or event projection is evaluated. -/
def observe (p : Program) (s : State) : Option ObservationKind :=
  match s.phase with
  | .parkObserved location =>
    if ParkConsumed p s location then some (.park s.episode location) else none
  | _ => if FreshHandler p s then some (.handlerEntry s.episode) else none

 theorem Observation.compute (meaning : Observation p s kind) : observe p s = some kind := by
  cases meaning with
  | handler fresh => simp [observe, fresh.2.2.1, fresh]
  | park phase consumed => simp [observe, phase, consumed]

 theorem observe_iff : observe p s = some kind ↔ Observation p s kind := by
  constructor
  · intro found
    unfold observe at found
    split at found
    next location phase =>
      split at found
      next consumed => cases found; exact .park phase consumed
      next absent => contradiction
    next phase =>
      split at found
      next fresh => cases found; exact .handler fresh
      next absent => contradiction
  · exact Observation.compute

 theorem observe_none_iff : observe p s = none ↔ ∀ kind, ¬ Observation p s kind := by
  rw [option_none_iff]
  constructor
  · intro absent kind meaning; exact absent kind meaning.compute
  · intro absent kind found; exact absent kind (observe_iff.mp found)

 theorem Observation.unique (left : Observation p s a) (right : Observation p s b) : a = b := by
  have same := left.compute.symm.trans right.compute
  exact Option.some.inj same

/-- Unused delivery is a stopping classification only when a covered observation is actually reached. -/
def PendingDelivery (env : Environment) (s : State) : Prop :=
  env.delivery.isSome = true ∧ s.deliveryUsed = false
instance : Decidable (PendingDelivery env s) := inferInstanceAs (Decidable (_ ∧ _))

end ANL.Boot.Runtime
