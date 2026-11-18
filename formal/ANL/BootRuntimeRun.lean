import ANL.BootRuntimeObservations

namespace ANL.Boot.Runtime

inductive StopReason where
  | observed (kind : ObservationKind)
  | unobserved (kind : ObservationKind)
  | blockedRead
  | ineligibleDelivery
  | exhausted
  | invalidState
  deriving DecidableEq, Repr

/-- `used` counts successful BootStep transitions, not attempts, expression fuel or host work. -/
structure RunResult where
  reason : StopReason
  state : State
  used : Nat
  deriving Repr

def RunResult.bump (result : RunResult) : RunResult := { result with used := result.used + 1 }

def observationResult (env : Environment) (s : State) (kind : ObservationKind) : RunResult :=
  ⟨if PendingDelivery env s then .unobserved kind else .observed kind, s, 0⟩

/-- Unchecked input API. Zero budget never invokes tick; observation has priority over exhaustion. -/
def runRaw (p : Program) (env : Environment) : Nat → State → RunResult
  | budget, s =>
    match observe p s with
    | some kind => observationResult env s kind
    | none =>
      match budget with
      | 0 => ⟨.exhausted, s, 0⟩
      | remaining + 1 =>
        match tickRaw p env s with
        | .advance next => (runRaw p env remaining next).bump
        | .blockedRead retained => ⟨.blockedRead, retained, 0⟩
        | .ineligibleDelivery retained => ⟨.ineligibleDelivery, retained, 0⟩
        | .invalidState retained => ⟨.invalidState, retained, 0⟩

/-- Unchecked resumption primitive. Its observed-entry precondition is supplied by resumeObserved. -/
def resumeRaw (p : Program) (env : Environment) : Nat → State → RunResult
  | 0, s => ⟨.exhausted, s, 0⟩
  | remaining + 1, s =>
    match tickRaw p env s with
    | .advance next => (runRaw p env remaining next).bump
    | .blockedRead retained => ⟨.blockedRead, retained, 0⟩
    | .ineligibleDelivery retained => ⟨.ineligibleDelivery, retained, 0⟩
    | .invalidState retained => ⟨.invalidState, retained, 0⟩

def run (p : Program) (input : ValidatedInput p) (budget : Nat) (s : State) : RunResult :=
  runRaw p input.raw budget s

def resumeObserved (p : Program) (input : ValidatedInput p) (budget : Nat) (s : State)
    (_observed : ∃ kind, Observation p s kind) : RunResult := resumeRaw p input.raw budget s

/-- Independent finite evaluation rules over observations and the accepted semantic transition relation. -/
inductive RunTo (p : Program) (env : Environment) : Nat → State → RunResult → Prop where
  | observed : Observation p state kind → ¬ PendingDelivery env state →
      RunTo p env budget state ⟨.observed kind, state, 0⟩
  | unobserved : Observation p state kind → PendingDelivery env state →
      RunTo p env budget state ⟨.unobserved kind, state, 0⟩
  | exhausted : (∀ kind, ¬ Observation p state kind) → RunTo p env 0 state ⟨.exhausted, state, 0⟩
  | blocked : (∀ kind, ¬ Observation p state kind) → BootOutcome p env state (.blockedRead state) →
      RunTo p env (budget + 1) state ⟨.blockedRead, state, 0⟩
  | ineligible : (∀ kind, ¬ Observation p state kind) → BootOutcome p env state (.ineligibleDelivery state) →
      RunTo p env (budget + 1) state ⟨.ineligibleDelivery, state, 0⟩
  | invalid : (∀ kind, ¬ Observation p state kind) → BootOutcome p env state (.invalidState state) →
      RunTo p env (budget + 1) state ⟨.invalidState, state, 0⟩
  | advance : (∀ kind, ¬ Observation p first kind) → BootStep p env first next →
      RunTo p env budget next result → RunTo p env (budget + 1) first result.bump

/-- A successful resume must take a real semantic step before ordinary observation handling resumes. -/
inductive ResumeTo (p : Program) (env : Environment) : Nat → State → RunResult → Prop where
  | exhausted : ResumeTo p env 0 state ⟨.exhausted, state, 0⟩
  | blocked : BootOutcome p env state (.blockedRead state) →
      ResumeTo p env (budget + 1) state ⟨.blockedRead, state, 0⟩
  | ineligible : BootOutcome p env state (.ineligibleDelivery state) →
      ResumeTo p env (budget + 1) state ⟨.ineligibleDelivery, state, 0⟩
  | invalid : BootOutcome p env state (.invalidState state) →
      ResumeTo p env (budget + 1) state ⟨.invalidState, state, 0⟩
  | advance : BootStep p env first next → RunTo p env budget next result →
      ResumeTo p env (budget + 1) first result.bump

end ANL.Boot.Runtime
