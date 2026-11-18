import ANL.BootSessionBounds

namespace ANL.Boot.Runtime.Session

/-- A reported row denotes an actual intermediate state; witnesses are propositions only. -/
def RowPrefix (p : Program) (env : Environment) (first : State) (total : Nat) (last : State) (row : Row) : Prop :=
  ∃ n middle m, BootStepsN p env n first middle ∧ BootStepsN p env m middle last ∧
    row.totalUsed = total + n ∧ row.eventEnd = middle.events.length ∧
    row.readCursor = middle.readCursor ∧ row.delivery = deliveryView env middle ∧
    FrontierAt p row.reason middle row.frontier

theorem SessionTo.row_prefix (meaning : SessionTo p env actions s previous index total rows result)
    (present : value ∈ result.rows) : value ∈ rows ∨ RowPrefix p env s total result.state value := by
  induction meaning with
  | done view | rejected _ view => cases view; exact .inl present
  | stopped allowed action row terminal view =>
    cases view
    simp only [List.mem_append, List.mem_singleton] at present
    rcases present with old | rfl
    · exact .inl old
    · obtain ⟨_, _, _, totalEq, reasonEq, eventEq, readEq, deliveryEq, frontierEq⟩ := row.fields
      exact .inr ⟨_, _, 0, action.prefix, .zero, totalEq, eventEq, readEq, deliveryEq, reasonEq ▸ frontierEq⟩
  | advanced allowed action row ongoing rest ih =>
    rcases ih present with old | later
    · simp only [List.mem_append, List.mem_singleton] at old
      rcases old with old | rfl
      · exact .inl old
      · obtain ⟨_, _, _, _, suffix, _⟩ := rest.summary
        obtain ⟨_, _, _, totalEq, reasonEq, eventEq, readEq, deliveryEq, frontierEq⟩ := row.fields
        exact .inr ⟨_, _, _, action.prefix, suffix, totalEq, eventEq, readEq, deliveryEq, reasonEq ▸ frontierEq⟩
    · obtain ⟨n, middle, m, beforeProof, suffix, totalEq, eventEq, readEq, deliveryEq, frontierEq⟩ := later
      exact .inr ⟨_, middle, m, action.prefix.append beforeProof, suffix,
        by simpa only [Nat.add_assoc] using totalEq, eventEq, readEq, deliveryEq, frontierEq⟩

theorem RowPrefix.events (beforeProof : RowPrefix p env first total last row) :
    ∃ middleEvents suffix, last.events = middleEvents ++ suffix ∧
      row.eventEnd = middleEvents.length ∧ last.events.take row.eventEnd = middleEvents := by
  obtain ⟨_, middle, _, _, steps, _, eventEq, _⟩ := beforeProof
  obtain ⟨suffix, eq, _⟩ := steps.ordered_event_prefix
  exact ⟨middle.events, suffix, eq, eventEq, by simp [eq, eventEq]⟩

theorem SessionTo.entry_row_events (meaning : SessionTo p env actions first none 0 0 [] result)
    (present : row ∈ result.rows) :
    ∃ n middle m, BootStepsN p env n first middle ∧ BootStepsN p env m middle result.state ∧
      row.totalUsed = n ∧ row.eventEnd = middle.events.length ∧
      result.state.events.take row.eventEnd = middle.events ∧ row.readCursor = middle.readCursor ∧
      row.delivery = deliveryView env middle ∧ FrontierAt p row.reason middle row.frontier := by
  rcases meaning.row_prefix present with impossible | beforeProof
  · cases impossible
  · obtain ⟨n, middle, m, before, after, totalEq, eventEq, readEq, deliveryEq, frontierEq⟩ := beforeProof
    obtain ⟨suffix, suffixEq, _⟩ := after.ordered_event_prefix
    exact ⟨n, middle, m, before, after, by simpa using totalEq, eventEq,
      by simp [suffixEq, eventEq], readEq, deliveryEq, frontierEq⟩

theorem SessionTo.checked_offsets (wf : WellFormedProgram p) (input : InputValid p env)
    (started : Start p env first) (meaning : SessionTo p env actions first none 0 0 [] result) :
    result.state.eventCount = result.state.events.length ∧ result.state.eventCount ≤ result.totalUsed ∧
      ∀ row ∈ result.rows, row.eventEnd ≤ row.totalUsed ∧ row.eventEnd ≤ result.state.eventCount := by
  obtain ⟨added, rowEq, totalEq, _, steps, _⟩ := meaning.summary
  have counts := checked_prefix_event_count wf input started steps
  simp only [Nat.zero_add] at totalEq
  refine ⟨counts.1, by omega, ?_⟩
  intro row present
  obtain ⟨n, middle, m, before, after, rowUsed, rowEvents, _, _, _, _⟩ := meaning.entry_row_events present
  have middleCounts := checked_prefix_event_count wf input started before
  obtain ⟨suffix, suffixEq, _⟩ := after.ordered_event_prefix
  refine ⟨?_, ?_⟩
  · rw [rowEvents, rowUsed, ← middleCounts.1]
    exact middleCounts.2
  · rw [counts.1, suffixEq, List.length_append, rowEvents]
    exact Nat.le_add_right _ _

theorem SessionTo.rows_not_invalid (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : SafetyInvariant p env s) (meaning : SessionTo p env actions s previous index total rows result)
    (old : ∀ row ∈ rows, row.reason ≠ .invalidState) :
    ∀ row ∈ result.rows, row.reason ≠ .invalidState := by
  induction meaning with
  | done view | rejected _ view => cases view; exact old
  | stopped _ action row _ view =>
    cases view
    intro value present
    simp only [List.mem_append, List.mem_singleton] at present
    rcases present with prior | rfl
    · exact old _ prior
    · rw [row.fields.2.2.2.2.1]
      exact (action.safety wf input safe).2
  | advanced _ action row _ _ ih =>
    apply ih (action.safety wf input safe).1
    intro value present
    simp only [List.mem_append, List.mem_singleton] at present
    rcases present with prior | rfl
    · exact old _ prior
    · rw [row.fields.2.2.2.2.1]
      exact (action.safety wf input safe).2

end ANL.Boot.Runtime.Session
