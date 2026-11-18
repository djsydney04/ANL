import ANL.BootSessionOffsets

namespace ANL.Boot.Runtime.Session

/-- Successive rows partition one ordered event prefix; suffixes exist only in Prop. -/
inductive EventSlices : List Event → List Row → List Event → Prop where
  | nil : EventSlices events [] events
  | cons : row.eventEnd = (before ++ added).length → added.length ≤ row.used →
      EventSlices (before ++ added) rows final → EventSlices before (row :: rows) final

theorem SessionTo.event_slices (meaning : SessionTo p env actions s previous index total rows result) :
    ∃ added, result.rows = rows ++ added ∧ EventSlices s.events added result.state.events := by
  induction meaning with
  | done view | rejected _ view => cases view; exact ⟨[], by simp, .nil⟩
  | stopped _ action row _ view =>
    cases view
    obtain ⟨suffix, eq, bound⟩ := action.prefix.ordered_event_prefix
    obtain ⟨_, _, used, _, _, eventEq, _⟩ := row.fields
    refine ⟨[_], rfl, ?_⟩
    rw [eq]
    exact .cons (eq ▸ eventEq) (used ▸ bound) .nil
  | @advanced previous s a ar index total value tail rows result _ action row _ rest ih =>
    obtain ⟨added, rowEq, slices⟩ := ih
    obtain ⟨suffix, eq, bound⟩ := action.prefix.ordered_event_prefix
    obtain ⟨_, _, used, _, _, eventEq, _⟩ := row.fields
    exact ⟨value :: added, by simpa only [List.append_assoc, List.singleton_append] using rowEq,
      .cons (eq ▸ eventEq) (used ▸ bound) (eq ▸ slices)⟩

theorem EventSlices.extension (slices : EventSlices before rows final) :
    ∃ suffix, final = before ++ suffix := by
  induction slices with
  | nil => exact ⟨[], by simp⟩
  | @cons before added rows final row _ _ _ ih =>
    obtain ⟨suffix, rfl⟩ := ih
    exact ⟨added ++ suffix, by simp [List.append_assoc]⟩

theorem EventSlices.growth (slices : EventSlices before rows final) (present : rows[i]? = some row) :
    ∃ prior suffix, final.take (row.eventEnd - suffix.length) = prior ∧
      final.take row.eventEnd = prior ++ suffix ∧ row.eventEnd = prior.length + suffix.length ∧
      suffix.length ≤ row.used ∧
      (i = 0 → prior = before) ∧
      (∀ j, i = j + 1 → ∃ earlier, rows[j]? = some earlier ∧ earlier.eventEnd = prior.length) := by
  induction slices generalizing i with
  | nil => simp at present
  | @cons before added rows final value eq bound rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at present
      subst row
      obtain ⟨suffix, finalEq⟩ := rest.extension
      refine ⟨before, added, ?_, ?_, ?_, bound, fun _ => rfl, ?_⟩
      · simp [eq, finalEq, List.append_assoc]
      · rw [eq, finalEq, List.take_left]
      · simpa only [List.length_append] using eq
      · intro j impossible; omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at present
      obtain ⟨prior, suffix, first, second, length, bound, initial, predecessor⟩ := ih present
      refine ⟨prior, suffix, first, second, length, bound, by omega, ?_⟩
      intro j indexEq
      have ji : j = i := by omega
      subst j
      cases i with
      | zero => exact ⟨value, rfl, by rw [initial rfl]; exact eq⟩
      | succ k =>
        obtain ⟨earlier, present, endEq⟩ := predecessor k rfl
        exact ⟨earlier, by simpa using present, endEq⟩

end ANL.Boot.Runtime.Session
