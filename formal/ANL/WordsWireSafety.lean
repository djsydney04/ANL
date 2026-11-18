import ANL.WordsWire

namespace ANL.Words.Wire

theorem checkCoreDocument_iff {text : String} {p : Program} :
    checkCoreDocument text = .ok p ↔ readCore text = .ok p ∧ WellFormedProgram p := by
  unfold checkCoreDocument
  cases hr : readCore text with
  | error e => simp [bind, Except.bind]
  | ok c =>
    simp only [bind, Except.bind]
    split
    · rename_i hc
      simp only [pure, Except.pure, Except.ok.injEq]
      constructor
      · intro h; subst c; exact ⟨rfl, checkProgram_iff.mp hc⟩
      · intro h; exact h.1
    · rename_i hc
      constructor
      · intro h; cases h
      · rintro ⟨h, hp⟩
        cases h
        exact False.elim (hc (checkProgram_iff.mpr hp))

theorem checkMirDocument_iff {text : String} {p : Mir.Program} :
    checkMirDocument text = .ok p ↔ readMir text = .ok p ∧ p.WellFormed := by
  unfold checkMirDocument
  cases hr : readMir text with
  | error e => simp [bind, Except.bind]
  | ok c =>
    simp only [bind, Except.bind]
    split
    · rename_i hc
      simp only [pure, Except.pure, Except.ok.injEq]
      constructor
      · intro h; subst c; exact ⟨rfl, (Mir.checkProgram_iff _).mp hc⟩
      · intro h; exact h.1
    · rename_i hc
      constructor
      · intro h; cases h
      · rintro ⟨h, hp⟩
        cases h
        exact False.elim (hc ((Mir.checkProgram_iff _).mpr hp))

theorem unsignedDigits_bound {bytes : List UInt8} {value result : Nat}
    (h : unsignedDigits bytes value = some result) : result ≤ wireNatMax := by
  induction bytes generalizing value with
  | nil =>
    simp only [unsignedDigits] at h
    split at h
    · cases h; assumption
    · cases h
  | cons byte rest ih =>
    simp only [unsignedDigits] at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact ih h

theorem unsignedText_bound {text : String} {value : Nat}
    (h : unsignedText text = some value) : value ≤ wireNatMax := by
  unfold unsignedText at h
  split at h
  · cases h
  · cases hd : unsignedDigits text.toUTF8.data.toList 0 with
    | none => simp only [hd, bind, Option.bind] at h; cases h
    | some found =>
      simp only [hd, bind, Option.bind] at h
      split at h
      · cases h; exact unsignedDigits_bound hd
      · cases h

theorem unsignedText_canonical {text : String} {value : Nat}
    (h : unsignedText text = some value) : toString value = text := by
  unfold unsignedText at h
  split at h
  · cases h
  · cases hd : unsignedDigits text.toUTF8.data.toList 0 with
    | none => simp only [hd, bind, Option.bind] at h; cases h
    | some found =>
      simp only [hd, bind, Option.bind] at h
      split at h
      · rename_i canonical
        cases h
        exact of_decide_eq_true canonical
      · cases h

end ANL.Words.Wire
