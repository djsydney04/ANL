import ANL.BootRuntimeTailLaws

namespace ANL.Boot.Runtime.Session

inductive ActionKind where
  | run | continue | resume
  deriving DecidableEq, Repr

structure Action where
  kind : ActionKind
  budget : Nat
  deriving DecidableEq, Repr

def ActionShape (actions : List Action) : Prop :=
  ∃ budget rest, actions = ⟨.run, budget⟩ :: rest ∧ ∀ action ∈ rest, action.kind ≠ .run

def checkShape : List Action → Bool
  | [] => false
  | first :: rest => first.kind == .run && rest.all (fun action => action.kind != .run)

def Nonterminal : StopReason → Prop
  | .observed _ | .unobserved _ | .exhausted => True
  | _ => False

inductive ObservationView (p : Program) (s : State) : Option ObservationKind → Prop where
  | absent : (∀ kind, ¬ Observation p s kind) → ObservationView p s none
  | present : Observation p s kind → ObservationView p s (some kind)

inductive Applicable (p : Program) (previous : Option StopReason) (s : State) : ActionKind → Prop where
  | fresh : previous = none → Applicable p previous s .run
  | continued : previous = some .exhausted → (∀ kind, ¬ Observation p s kind) → Applicable p previous s .continue
  | resumed : previous = some reason → Nonterminal reason → Observation p s kind → Applicable p previous s .resume

def nextKind (previous : StopReason) (observed : Option ObservationKind) : Option ActionKind :=
  match previous with
  | .blockedRead | .ineligibleDelivery | .invalidState => none
  | _ => match observed with
    | some _ => some .resume
    | none => if previous = .exhausted then some .continue else none

structure Frontier where
  observation : Option ObservationKind
  next : Option ActionKind
  deriving DecidableEq, Repr

/-- One classifier result is shared by the observation and next-action views. -/
def frontier (p : Program) (previous : StopReason) (s : State) : Frontier :=
  let observed := observe p s
  ⟨observed, nextKind previous observed⟩

def applicable (p : Program) (previous : Option StopReason) (s : State) (kind : ActionKind) : Bool :=
  match previous with
  | none => kind == .run
  | some reason => (frontier p reason s).next == some kind

inductive DeliveryView where
  | absent | pending | used
  deriving DecidableEq, Repr

def deliveryView (env : Environment) (s : State) : DeliveryView :=
  match env.delivery with
  | none => .absent
  | some _ => if s.deliveryUsed then .used else .pending

structure Row where
  index : Nat
  action : Action
  used : Nat
  totalUsed : Nat
  reason : StopReason
  frontier : Frontier
  eventEnd : Nat
  readCursor : Nat
  delivery : DeliveryView
  deriving Repr

/-- Rows retain only constant-shape endpoint views, never a previous State or event list. -/
def makeRow (p : Program) (env : Environment) (index : Nat) (action : Action)
    (total : Nat) (result : RunResult) : Row :=
  ⟨index, action, result.used, total + result.used, result.reason,
    frontier p result.reason result.state, result.state.eventCount,
    result.state.readCursor, deliveryView env result.state⟩

def actionRun (p : Program) (env : Environment) (action : Action) (s : State) : RunResult :=
  match action.kind with
  | .resume => resumeTailRaw p env action.budget s
  | .run | .continue => runTailRaw p env action.budget s

inductive ActionTo (p : Program) (env : Environment) : Action → State → RunResult → Prop where
  | run : RunTo p env budget s result → ActionTo p env ⟨.run, budget⟩ s result
  | continued : RunTo p env budget s result → ActionTo p env ⟨.continue, budget⟩ s result
  | resumed : ResumeTo p env budget s result → ActionTo p env ⟨.resume, budget⟩ s result

inductive Ending where
  | done | blocked | ineligible | invalid
  | rejected (index : Nat)
  deriving DecidableEq, Repr

def terminal : StopReason → Option Ending
  | .blockedRead => some .blocked
  | .ineligibleDelivery => some .ineligible
  | .invalidState => some .invalid
  | _ => none

structure Result where
  state : State
  previous : StopReason
  totalUsed : Nat
  rows : List Row
  ending : Ending
  frontier : Frontier
  deriving Repr

/-- The final projection calls the classifier once, including after an applicability rejection. -/
def finish (p : Program) (s : State) (previous : Option StopReason)
    (total : Nat) (reverseRows : List Row) (ending : Ending) : Result :=
  let reason := previous.getD .exhausted
  ⟨s, reason, total, reverseRows.reverse, ending, frontier p reason s⟩

def loop (p : Program) (env : Environment) : List Action → State → Option StopReason →
    Nat → Nat → List Row → Result
  | [], s, previous, _, total, reverseRows => finish p s previous total reverseRows .done
  | action :: rest, s, previous, index, total, reverseRows =>
    if applicable p previous s action.kind then
      let result := actionRun p env action s
      let row := makeRow p env index action total result
      match terminal result.reason with
      | some ending => finish p result.state (some result.reason) (total + result.used) (row :: reverseRows) ending
      | none => loop p env rest result.state (some result.reason) (index + 1) (total + result.used) (row :: reverseRows)
    else finish p s previous total reverseRows (.rejected index)

inductive StartResult where
  | malformedShape | invalidStart
  | ran (result : Result)
  deriving Repr

def sessionRaw (p : Program) (env : Environment) (actions : List Action) : StartResult :=
  if checkShape actions then
    match startRaw p env with
    | none => .invalidStart
    | some first => .ran (loop p env actions first none 0 0 [])
  else .malformedShape

def session (p : Program) (input : ValidatedInput p) (actions : List Action) : StartResult :=
  sessionRaw p input.raw actions

end ANL.Boot.Runtime.Session
