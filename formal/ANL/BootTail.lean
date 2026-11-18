import ANL.BootSyntax

namespace ANL.Boot

open ANL.Words

theorem isPark_iff : isPark e = true ↔ e = park := by
  unfold isPark
  split
  · simp [park]
  · simp_all [park]

theorem isHandler_iff : isHandler e = true ↔ e = handler := by
  unfold isHandler
  split
  · simp [handler, isPark_iff, and_left_comm, and_comm]
  · simp_all [handler]

theorem park_typed : HasType sigs Γ R park unitTy :=
  .whileE (.lit (v := .bool true)) (.lit (v := .unit))

theorem handler_typed : HasType sigs Γ R handler unitTy :=
  .letE park_typed (.lit (v := .unit))

theorem HasTail.search (h : HasTail e) : (designatedTail e).isSome = true := by
  induction h with
  | park => rfl
  | letValue _ ih | mutValue _ ih =>
    simp only [designatedTail, isPark, Bool.false_eq_true, ↓reduceIte]
    cases ha : designatedTail _ <;> simp_all
  | letBody _ ih | mutBody _ ih =>
    simp only [designatedTail, isPark, Bool.false_eq_true, ↓reduceIte]
    cases ha : designatedTail _ <;> simp_all

theorem designatedTail_sound (h : designatedTail e = some path) : SelectedTail e path := by
  induction e using Term.rec
    (motive_2 := fun _ => True) generalizing path with
  | letE t a b ia ib =>
    simp only [designatedTail, isPark, Bool.false_eq_true, ↓reduceIte] at h
    cases ha : designatedTail a with
    | some found =>
      simp only [ha, Option.some.injEq] at h
      subst path
      exact .letValue (ia ha)
    | none =>
      simp only [ha, Option.map_eq_some_iff] at h
      obtain ⟨found, hb, rfl⟩ := h
      exact .letBody (fun tail => by simpa [ha] using tail.search) (ib hb)
  | letMut t a b ia ib =>
    simp only [designatedTail, isPark, Bool.false_eq_true, ↓reduceIte] at h
    cases ha : designatedTail a with
    | some found =>
      simp only [ha, Option.some.injEq] at h
      subst path
      exact .mutValue (ia ha)
    | none =>
      simp only [ha, Option.map_eq_some_iff] at h
      obtain ⟨found, hb, rfl⟩ := h
      exact .mutBody (fun tail => by simpa [ha] using tail.search) (ib hb)
  | nil => trivial
  | cons _ _ _ _ => trivial
  | whileE t c b _ _ =>
    simp only [designatedTail] at h
    split at h
    next hp =>
      have eq := isPark_iff.mp hp
      cases h
      rw [eq]
      exact .park
    next => contradiction
  | _ => simp [designatedTail, isPark] at h

theorem SelectedTail.hasTail (h : SelectedTail e path) : HasTail e := by
  induction h with
  | park => exact .park
  | letValue _ ih => exact .letValue ih
  | letBody _ _ ih => exact .letBody ih
  | mutValue _ ih => exact .mutValue ih
  | mutBody _ _ ih => exact .mutBody ih

theorem designatedTail_isSome_iff : (designatedTail e).isSome = true ↔ HasTail e := by
  constructor
  · intro h
    cases eq : designatedTail e with
    | none => simp [eq] at h
    | some path => exact (designatedTail_sound eq).hasTail
  · exact HasTail.search

theorem noTail_search (h : ¬ HasTail e) : designatedTail e = none := by
  cases eq : designatedTail e with
  | none => rfl
  | some found => exact False.elim (h (designatedTail_sound eq).hasTail)

theorem SelectedTail.search (h : SelectedTail e path) : designatedTail e = some path := by
  induction h with
  | park => rfl
  | letValue _ ih | mutValue _ ih => simp [designatedTail, isPark, ih]
  | letBody absent _ ih | mutBody absent _ ih =>
    have ha := noTail_search absent
    simp [designatedTail, isPark, ha, ih]

theorem designatedTail_iff : designatedTail e = some path ↔ SelectedTail e path :=
  ⟨designatedTail_sound, SelectedTail.search⟩

theorem SelectedTail.unique (left : SelectedTail e a) (right : SelectedTail e b) : a = b := by
  exact Option.some.inj (left.search.symm.trans right.search)

theorem noNormalReturn_iff : NoNormalReturn sigs Γ R e t ↔
    HasType sigs Γ R e t ∧ (designatedTail e).isSome = true := by
  constructor
  · intro h; exact ⟨h.typed, h.tail.search⟩
  · rintro ⟨typed, tail⟩; exact ⟨typed, designatedTail_isSome_iff.mp tail⟩

theorem handler_selected : SelectedTail handler [.value] := .letValue .park

end ANL.Boot
