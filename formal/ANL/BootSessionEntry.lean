import ANL.BootSessionCostProofs
import ANL.BootSessionSlices

namespace ANL.Boot.Runtime.Session

/-- Gateway source-call accounting. Pre-start failures perform no classifier or tick calls. -/
inductive GatewayCalls (p : Program) (env : Environment) (actions : List Action) : StartResult → Nat → Nat → Prop where
  | malformed : ¬ ActionShape actions → GatewayCalls p env actions .malformedShape 0 0
  | invalid : ActionShape actions → (∀ s, ¬ Start p env s) → GatewayCalls p env actions .invalidStart 0 0
  | ran : ActionShape actions → Start p env first →
      SessionCalls p env actions first none 0 0 [] result observations ticks →
      GatewayCalls p env actions (.ran result) observations ticks

theorem SessionTo.deterministic (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : SafetyInvariant p env s) (left : SessionTo p env actions s previous index total rows a)
    (right : SessionTo p env actions s previous index total rows b) : a = b := by
  exact (left.compute wf input safe (reverseRows := rows.reverse) (by simp)).symm.trans
    (right.compute wf input safe (reverseRows := rows.reverse) (by simp))

theorem sessionRaw_ran_iff (wf : WellFormedProgram p) (input : InputValid p env) :
    sessionRaw p env actions = .ran result ↔ ActionShape actions ∧
      ∃ first, Start p env first ∧ SessionTo p env actions first none 0 0 [] result := by
  constructor
  · intro output
    by_cases shape : checkShape actions = true
    · simp only [sessionRaw, shape, ite_eq_left] at output
      cases started : startRaw p env with
      | none => simp only [started] at output; contradiction
      | some first =>
        simp only [started, StartResult.ran.injEq] at output
        rw [← output]
        exact ⟨checkShape_iff.mp shape, first, startRaw_iff.mp started,
          loop_sound (reverseRows := []) wf input ((startRaw_iff.mp started).safety wf input)⟩
    · simp only [sessionRaw, shape] at output
      contradiction
  · rintro ⟨shape, first, started, meaning⟩
    simp only [sessionRaw, checkShape_iff.mpr shape, ite_eq_left, startRaw_iff.mpr started]
    exact congrArg StartResult.ran (meaning.compute wf input (started.safety wf input) rfl)

theorem sessionRaw_malformed_iff : sessionRaw p env actions = .malformedShape ↔ ¬ ActionShape actions := by
  unfold sessionRaw
  split
  · rename_i shape
    cases startRaw p env <;> simp [checkShape_iff.mp shape]
  · rename_i shape
    simp only [true_iff]
    exact fun h => shape (checkShape_iff.mpr h)

theorem gateway_calls_iff (wf : WellFormedProgram p) (input : InputValid p env) :
    sessionRaw p env actions = result ↔ ∃ observations ticks, GatewayCalls p env actions result observations ticks := by
  constructor
  · intro eq
    by_cases shape : ActionShape actions
    · obtain ⟨first, started⟩ := Start.exists wf input
      have meaning := loop_sound (actions := actions) (previous := none) (index := 0) (total := 0)
        (reverseRows := []) wf input (started.safety wf input)
      obtain ⟨o, t, calls⟩ := meaning.calls
      have output : sessionRaw p env actions = .ran (loop p env actions first none 0 0 []) :=
        (sessionRaw_ran_iff wf input).mpr ⟨shape, first, started, meaning⟩
      rw [output] at eq
      cases eq
      exact ⟨o, t, .ran shape started calls⟩
    · rw [sessionRaw_malformed_iff.mpr shape] at eq
      cases eq
      exact ⟨0, 0, .malformed shape⟩
  · rintro ⟨o, t, calls⟩
    cases calls with
    | malformed shape => exact sessionRaw_malformed_iff.mpr shape
    | invalid shape noStart => obtain ⟨s, started⟩ := Start.exists wf input; exact False.elim (noStart s started)
    | ran shape started calls => exact (sessionRaw_ran_iff wf input).mpr ⟨shape, _, started, calls.meaning⟩

theorem sessionRaw_no_invalid_start (wf : WellFormedProgram p) (input : InputValid p env) :
    sessionRaw p env actions ≠ .invalidStart := by
  intro eq
  obtain ⟨o, t, calls⟩ := (gateway_calls_iff wf input).mp eq
  cases calls with
  | invalid _ noStart => obtain ⟨s, started⟩ := Start.exists wf input; exact noStart s started

theorem SessionTo.total (meaning : SessionTo p env actions first none 0 0 [] result) :
    result.totalUsed = usedRows result.rows := by
  obtain ⟨added, rows, total, _⟩ := meaning.summary
  simpa only [rows, List.nil_append, Nat.zero_add] using total

theorem sessionRaw_checked (wf : WellFormedProgram p) (input : InputValid p env)
    (output : sessionRaw p env actions = .ran result) :
    ∃ first, Start p env first ∧ BootStepsN p env result.totalUsed first result.state ∧
      SafetyInvariant p env result.state ∧ result.ending ≠ .invalid ∧
      0 < result.rows.length ∧ result.totalUsed ≤ budgets actions ∧
      result.state.eventCount = result.state.events.length ∧ result.state.eventCount ≤ result.totalUsed := by
  obtain ⟨shape, first, started, meaning⟩ := (sessionRaw_ran_iff wf input).mp output
  obtain ⟨added, rows, total, bound, steps, _⟩ := meaning.summary
  have safe := meaning.safe wf input (started.safety wf input)
  have offsets := meaning.checked_offsets wf input started
  simp only [Nat.zero_add] at total
  exact ⟨first, started, total ▸ steps, safe.1, safe.2, meaning.nonempty shape,
    total ▸ bound, offsets.1, offsets.2.1⟩

theorem GatewayCalls.prestart_zero (calls : GatewayCalls p env actions result observations ticks)
    (prestart : result = .malformedShape ∨ result = .invalidStart) : observations = 0 ∧ ticks = 0 := by
  cases calls <;> simp_all

theorem GatewayCalls.poststart_counts (calls : GatewayCalls p env actions (.ran result) observations ticks) :
    0 < result.rows.length ∧ observations = result.totalUsed + ordinaryRows result.rows +
      2 * result.rows.length + rejectedCount result.ending ∧
      ticks = result.totalUsed + terminalCount result.ending ∧
      observations ≤ budgets actions + 3 * actions.length ∧ ticks ≤ budgets actions := by
  cases calls with
  | ran shape started calls =>
    obtain ⟨positive, oEq, tEq, tBound⟩ := calls.entry_counts shape
    exact ⟨positive, calls.meaning.total ▸ oEq, calls.meaning.total ▸ tEq,
      (calls.entry_bounds shape).1, tBound⟩

end ANL.Boot.Runtime.Session
