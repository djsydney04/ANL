import ANL.BootSessionCalls

namespace ANL.Boot.Runtime.Session

theorem RowAt.fields (row : RowAt p env index action total result value) :
    value.index = index ∧ value.action = action ∧ value.used = result.used ∧
    value.totalUsed = total + result.used ∧ value.reason = result.reason ∧
    value.eventEnd = result.state.events.length ∧ value.readCursor = result.state.readCursor ∧
    value.delivery = deliveryView env result.state ∧ FrontierAt p result.reason result.state value.frontier := by
  cases row with | endpoint view => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, view⟩

theorem SessionTo.summary (meaning : SessionTo p env actions s previous index total rows result) :
    ∃ added, result.rows = rows ++ added ∧ result.totalUsed = total + usedRows added ∧
      usedRows added ≤ budgets actions ∧ BootStepsN p env (usedRows added) s result.state ∧
      added.length ≤ actions.length := by
  induction meaning with
  | done view | rejected _ view =>
    cases view
    exact ⟨[], by simp, by simp [usedRows], by simp [usedRows], .zero, by simp⟩
  | stopped allowed action row stopped view =>
    cases view
    obtain ⟨_, _, used, _, _, _, _, _, _⟩ := row.fields
    refine ⟨[_], rfl, ?_, ?_, ?_, by simp⟩
    · simp [usedRows, used]
    · simpa only [usedRows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, used,
        budgets] using Nat.le_trans action.bound (Nat.le_add_right _ _)
    · simpa [usedRows, used] using action.prefix
  | @advanced previous s a ar index total value tail rows result allowed action row ongoing rest ih =>
    obtain ⟨added, rowEq, totalEq, bound, steps, length⟩ := ih
    obtain ⟨_, _, used, _, _, _, _, _, _⟩ := row.fields
    refine ⟨value :: added, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [List.append_assoc, List.singleton_append] using rowEq
    · simp only [usedRows, List.map_cons, List.sum_cons, used]
      simpa only [usedRows, Nat.add_assoc] using totalEq
    · simp only [usedRows, List.map_cons, List.sum_cons, used, budgets, List.map_cons, List.sum_cons]
      have actionBound := action.bound
      simp only [usedRows, budgets] at bound
      omega
    · simpa only [usedRows, List.map_cons, List.sum_cons, used] using action.prefix.append steps
    · simp only [List.length_cons]
      omega

theorem TerminalReason.invalid_iff (terminal : TerminalReason reason ending) :
    ending = .invalid ↔ reason = .invalidState := by cases terminal <;> simp

theorem TerminalReason.not_rejected (terminal : TerminalReason reason ending) :
    ending ≠ .rejected index := by cases terminal <;> simp

theorem SessionTo.safe (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : SafetyInvariant p env s) (meaning : SessionTo p env actions s previous index total rows result) :
    SafetyInvariant p env result.state ∧ result.ending ≠ .invalid := by
  induction meaning with
  | done view | rejected _ view => cases view; exact ⟨safe, by intro h; contradiction⟩
  | stopped _ action _ terminal view =>
    have nextSafe := action.safety wf input safe
    cases view
    refine ⟨nextSafe.1, ?_⟩
    intro h
    exact nextSafe.2 (terminal.invalid_iff.mp h)
  | advanced _ action _ _ _ ih => exact ih (action.safety wf input safe).1

theorem SessionTo.rejection_index (meaning : SessionTo p env actions s previous index total rows result)
    (rejected : result.ending = .rejected failed) :
    failed = index + (result.rows.length - rows.length) ∧ result.rows.length - rows.length < actions.length := by
  induction meaning with
  | done view => cases view; contradiction
  | rejected _ view => cases view; cases rejected; simp
  | stopped _ _ _ terminal view => cases view; exact False.elim (terminal.not_rejected rejected)
  | advanced _ _ _ _ rest ih =>
    have tail := ih rejected
    obtain ⟨added, rowEq, _, _, _, _⟩ := rest.summary
    simp only [rowEq, List.length_append, List.length_cons, List.length_nil] at *
    omega

theorem SessionTo.action_prefix (meaning : SessionTo p env actions s previous index total rows result) :
    result.rows.map Row.action = rows.map Row.action ++
      actions.take (result.rows.length - rows.length) := by
  induction meaning with
  | done view | rejected _ view => cases view; simp
  | stopped _ _ row _ view =>
    cases view
    have actionEq := row.fields.2.1
    simp [actionEq]
  | @advanced previous s a ar index total value tail rows result _ _ row _ rest ih =>
    have actionEq := row.fields.2.1
    obtain ⟨added, rowEq, _, _, _, _⟩ := rest.summary
    simp only [rowEq, List.length_append, List.length_singleton, List.map_append, List.map_cons,
      List.map_nil, actionEq] at *
    have arithmetic₁ : rows.length + 1 + added.length - (rows.length + 1) = added.length := by omega
    have arithmetic₂ : rows.length + 1 + added.length - rows.length = added.length + 1 := by omega
    rw [arithmetic₁] at ih
    rw [arithmetic₂]
    simpa [List.take_succ_cons, List.append_assoc] using ih

theorem SessionTo.nonempty (meaning : SessionTo p env actions s none index total [] result)
    (shape : ActionShape actions) : 0 < result.rows.length := by
  obtain ⟨budget, rest, rfl, _⟩ := shape
  cases meaning with
  | rejected denied _ => exact False.elim (denied (.fresh rfl))
  | stopped _ _ _ _ view => cases view; simp
  | advanced _ _ _ _ rest =>
    obtain ⟨added, rowEq, _, _, _, _⟩ := rest.summary
    simp [rowEq]

end ANL.Boot.Runtime.Session
