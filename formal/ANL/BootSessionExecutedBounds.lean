import ANL.BootSessionEntry

namespace ANL.Boot.Runtime.Session

def rowBudgets (rows : List Row) : Nat := (rows.map (fun row => row.action.budget)).sum

theorem ActionCalls.block_strict (calls : ActionCalls p env action s result observations ticks)
    (blocked : blocker result.reason = 1) : result.used < action.budget := by
  have count := calls.counts.2
  have bound := calls.bounds.2
  omega

theorem SessionCalls.executed_budget (calls : SessionCalls p env actions s previous index total rows result observations ticks) :
    ticks + rowBudgets rows ≤ rowBudgets result.rows := by
  induction calls with
  | done view | rejected _ view => cases view; simp
  | stopped _ action row _ view =>
    cases view
    have actionEq := row.fields.2.1
    have bound := action.bounds.2
    simp only [rowBudgets, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, actionEq]
    omega
  | advanced _ action row _ _ ih =>
    have actionEq := row.fields.2.1
    have bound := action.bounds.2
    simp only [rowBudgets, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, actionEq] at ih ⊢
    omega

theorem SessionCalls.entry_executed_budget
    (calls : SessionCalls p env actions first none 0 0 [] result observations ticks) :
    ticks ≤ rowBudgets result.rows := by simpa [rowBudgets] using calls.executed_budget

/-- Explicit arithmetic order of the appended report rows. -/
inductive RowOrder : Nat → Nat → List Row → Prop where
  | nil : RowOrder index total []
  | cons : row.index = index → row.totalUsed = total + row.used →
      RowOrder (index + 1) (total + row.used) rows → RowOrder index total (row :: rows)

theorem SessionTo.row_order {total : Nat} (meaning : SessionTo p env actions s previous index total rows result) :
    ∃ added, result.rows = rows ++ added ∧ RowOrder index total added := by
  induction meaning with
  | done view | rejected _ view => cases view; exact ⟨[], by simp, .nil⟩
  | stopped _ _ row _ view =>
    cases view
    obtain ⟨indexEq, _, used, totalEq, _⟩ := row.fields
    exact ⟨[_], rfl, .cons indexEq (used ▸ totalEq) .nil⟩
  | @advanced previous s a ar index total value tail rows result _ _ row _ _ ih =>
    obtain ⟨added, rowEq, order⟩ := ih
    obtain ⟨indexEq, _, used, totalEq, _⟩ := row.fields
    exact ⟨value :: added, by simpa only [List.append_assoc, List.singleton_append] using rowEq,
      .cons indexEq (used ▸ totalEq) (used ▸ order)⟩

theorem RowOrder.at (order : RowOrder index total rows) (present : rows[i]? = some row) :
    row.index = index + i ∧ row.totalUsed = total + usedRows (rows.take (i + 1)) := by
  induction order generalizing i with
  | nil => simp at present
  | @cons value index total rows indexEq totalEq rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at present
      subst row
      exact ⟨by simpa using indexEq, by simpa [usedRows] using totalEq⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at present
      obtain ⟨position, used⟩ := ih present
      exact ⟨by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using position,
        by simpa [usedRows, Nat.add_assoc] using used⟩

theorem SessionTo.entry_row_order (meaning : SessionTo p env actions first none 0 0 [] result)
    (present : result.rows[i]? = some row) :
    row.index = i ∧ row.totalUsed = usedRows (result.rows.take (i + 1)) := by
  obtain ⟨added, eq, order⟩ := meaning.row_order
  simp only [List.nil_append] at eq
  rw [eq] at present ⊢
  simpa using order.at present

end ANL.Boot.Runtime.Session
