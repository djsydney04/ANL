import ANL.BootSessionBounds

namespace ANL.Boot.Runtime.Session

/-- The first reached action has no applicability classifier. Empty loops still report once. -/
def freshDiscount : List Action → Option StopReason → Nat
  | _ :: _, none => 1
  | _, _ => 0

theorem application_discount : applicationCalls previous + freshDiscount (action :: rest) previous = 1 := by
  cases previous <;> rfl

theorem TerminalReason.counts (terminal : TerminalReason reason ending) :
    blocker reason = 1 ∧ terminalCount ending = 1 ∧ rejectedCount ending = 0 := by
  cases terminal <;> exact ⟨rfl, rfl, rfl⟩

theorem Nonterminal.blocker (ongoing : Nonterminal reason) : blocker reason = 0 := by
  cases reason <;> simp_all [Nonterminal, Session.blocker]

theorem SessionCalls.counts (calls : SessionCalls p env actions s previous index total rows result observations ticks) :
    ∃ added, result.rows = rows ++ added ∧
      observations + freshDiscount actions previous =
        usedRows added + ordinaryRows added + 2 * added.length + rejectedCount result.ending + 1 ∧
      ticks = usedRows added + terminalCount result.ending ∧ ticks ≤ budgets actions := by
  induction calls with
  | done view =>
    cases view
    exact ⟨[], by simp, by simp [freshDiscount, usedRows, ordinaryRows, rejectedCount],
      by simp [usedRows, terminalCount], by simp [budgets]⟩
  | @rejected previous s a total rows index result rest denied view =>
    cases view
    refine ⟨[], by simp, ?_, by simp [usedRows, terminalCount], by simp⟩
    cases previous <;> rfl
  | @stopped previous s a ar o t index total value ending rows result tail allowed action row terminal view =>
    cases view
    obtain ⟨_, actionEq, used, _, _, _, _, _, _⟩ := row.fields
    obtain ⟨oEq, tEq⟩ := action.counts
    obtain ⟨blockEq, terminalEq, rejectedEq⟩ := terminal.counts
    have discount := application_discount (previous := previous) (action := a) (rest := tail)
    refine ⟨[_], rfl, ?_, ?_, ?_⟩
    · simp only [usedRows, ordinaryRows, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero, used, actionEq, List.length_singleton, rejectedEq]
      omega
    · simpa [usedRows, used, blockEq, terminalEq] using tEq
    · exact Nat.le_trans action.bounds.2 (Nat.le_add_right _ _)
  | @advanced previous s a ar o t index total value tail rows result ro rt allowed action row ongoing rest ih =>
    obtain ⟨added, rowEq, oEq, tEq, bound⟩ := ih
    obtain ⟨_, actionEq, used, _, _, _, _, _, _⟩ := row.fields
    obtain ⟨ao, atick⟩ := action.counts
    have blockEq := ongoing.blocker
    have discount := application_discount (previous := previous) (action := a) (rest := tail)
    simp only [freshDiscount, Nat.add_zero] at oEq
    refine ⟨value :: added, ?_, ?_, ?_, ?_⟩
    · simpa only [List.append_assoc, List.singleton_append] using rowEq
    · simp only [usedRows, ordinaryRows, List.map_cons, List.sum_cons, used, actionEq, List.length_cons]
      simp only [usedRows, ordinaryRows] at oEq
      omega
    · simp only [usedRows, List.map_cons, List.sum_cons, used]
      simp only [usedRows] at tEq
      omega
    · have actionBound := action.bounds.2
      change t + rt ≤ a.budget + budgets tail
      omega

theorem ordinaryRows_bound : ordinaryRows rows ≤ rows.length := by
  induction rows with
  | nil => simp [ordinaryRows]
  | cons row rest ih =>
    have one : ordinary row.action ≤ 1 := by cases h : row.action.kind <;> simp [ordinary, h]
    simp only [ordinaryRows, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

theorem SessionCalls.entry_counts (calls : SessionCalls p env actions s none 0 0 [] result observations ticks)
    (shape : ActionShape actions) :
    0 < result.rows.length ∧ observations = usedRows result.rows + ordinaryRows result.rows +
      2 * result.rows.length + rejectedCount result.ending ∧
      ticks = usedRows result.rows + terminalCount result.ending ∧ ticks ≤ budgets actions := by
  have nonempty := calls.meaning.nonempty shape
  obtain ⟨added, rowEq, obsEq, tickEq, bound⟩ := calls.counts
  simp only [List.nil_append] at rowEq
  obtain ⟨budget, rest, rfl, _⟩ := shape
  simp only [freshDiscount] at obsEq
  refine ⟨nonempty, ?_, ?_, bound⟩
  · simpa only [rowEq] using Nat.add_right_cancel obsEq
  · simpa only [rowEq] using tickEq

theorem SessionCalls.entry_bounds (calls : SessionCalls p env actions s none 0 0 [] result observations ticks)
    (shape : ActionShape actions) : observations ≤ budgets actions + 3 * actions.length ∧ ticks ≤ budgets actions := by
  obtain ⟨positive, obsEq, tickEq, ticksBound⟩ := calls.entry_counts shape
  obtain ⟨added, rowEq, totalEq, usedBound, steps, lengthBound⟩ := calls.meaning.summary
  simp only [List.nil_append] at rowEq
  rw [← rowEq] at usedBound lengthBound
  have ordinaryBound := ordinaryRows_bound (rows := result.rows)
  refine ⟨?_, ticksBound⟩
  cases endingEq : result.ending with
  | rejected failed =>
    have strict := (calls.meaning.rejection_index endingEq).2
    simp only [List.length_nil, Nat.sub_zero] at strict
    simp only [endingEq, rejectedCount] at obsEq
    omega
  | done | blocked | ineligible | invalid =>
    simp only [endingEq, rejectedCount] at obsEq
    omega

theorem SessionCalls.at_most_one_block (calls : SessionCalls p env actions s none 0 0 [] result observations ticks)
    (shape : ActionShape actions) : ticks ≤ usedRows result.rows + 1 := by
  have eq := (calls.entry_counts shape).2.2.1
  cases h : result.ending <;> simp_all [terminalCount]

end ANL.Boot.Runtime.Session
