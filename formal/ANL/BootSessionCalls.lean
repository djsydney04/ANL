import ANL.BootSessionRunnerCalls

namespace ANL.Boot.Runtime.Session

def applicationCalls : Option StopReason → Nat
  | none => 0
  | some _ => 1

def rejectedCount : Ending → Nat
  | .rejected _ => 1
  | _ => 0

def terminalCount : Ending → Nat
  | .blocked | .ineligible | .invalid => 1
  | _ => 0

def usedRows (rows : List Row) : Nat := (rows.map Row.used).sum
def ordinaryRows (rows : List Row) : Nat := (rows.map (fun row => ordinary row.action)).sum
def budgets (actions : List Action) : Nat := (actions.map Action.budget).sum

/-- Source-call sites: applicability, companion, one row projection, and one final projection.
    All counts are inferred by constructors. No bound or future result is a premise. -/
inductive SessionCalls (p : Program) (env : Environment) : List Action → State → Option StopReason →
    Nat → Nat → List Row → Result → Nat → Nat → Prop where
  | done : ResultAt p s previous total rows .done result →
      SessionCalls p env [] s previous index total rows result 1 0
  | rejected : ¬ Applicable p previous s action.kind →
      ResultAt p s previous total rows (.rejected index) result →
      SessionCalls p env (action :: rest) s previous index total rows result (applicationCalls previous + 1) 0
  | stopped : Applicable p previous s action.kind → ActionCalls p env action s actionResult observations ticks →
      RowAt p env index action total actionResult row → TerminalReason actionResult.reason ending →
      ResultAt p actionResult.state (some actionResult.reason) (total + actionResult.used) (rows ++ [row]) ending result →
      SessionCalls p env (action :: rest) s previous index total rows result
        (applicationCalls previous + observations + 2) ticks
  | advanced : Applicable p previous s action.kind → ActionCalls p env action s actionResult observations ticks →
      RowAt p env index action total actionResult row → Nonterminal actionResult.reason →
      SessionCalls p env rest actionResult.state (some actionResult.reason) (index + 1)
        (total + actionResult.used) (rows ++ [row]) result remainingObservations remainingTicks →
      SessionCalls p env (action :: rest) s previous index total rows result
        (applicationCalls previous + observations + 1 + remainingObservations) (ticks + remainingTicks)

theorem SessionCalls.meaning (calls : SessionCalls p env actions s previous index total rows result observations ticks) :
    SessionTo p env actions s previous index total rows result := by
  induction calls with
  | done view => exact .done view
  | rejected denied view => exact .rejected denied view
  | stopped allowed action row terminal view => exact .stopped allowed action.meaning row terminal view
  | advanced allowed action row ongoing _ ih => exact .advanced allowed action.meaning row ongoing ih

theorem SessionTo.calls (meaning : SessionTo p env actions s previous index total rows result) :
    ∃ observations ticks, SessionCalls p env actions s previous index total rows result observations ticks := by
  induction meaning with
  | done view => exact ⟨1, 0, .done view⟩
  | rejected denied view => exact ⟨_, 0, .rejected denied view⟩
  | stopped allowed action row terminal view =>
    obtain ⟨o, t, work⟩ := action.calls
    exact ⟨_, _, .stopped allowed work row terminal view⟩
  | advanced allowed action row ongoing _ ih =>
    obtain ⟨o, t, work⟩ := action.calls
    obtain ⟨ro, rt, rest⟩ := ih
    exact ⟨_, _, .advanced allowed work row ongoing rest⟩

theorem loop_calls_iff (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : SafetyInvariant p env s) :
    loop p env actions s previous index total reverseRows = result ↔
      ∃ observations ticks, SessionCalls p env actions s previous index total reverseRows.reverse result observations ticks := by
  constructor
  · intro eq; rw [← eq]; exact (loop_sound wf input safe).calls
  · rintro ⟨_, _, calls⟩; exact calls.meaning.compute wf input safe rfl

end ANL.Boot.Runtime.Session
