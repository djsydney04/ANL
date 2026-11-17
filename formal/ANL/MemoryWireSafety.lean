import ANL.MemoryWire

namespace ANL.Memory.Wire

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

theorem checkDocuments_iff {ct mt : String} {c : Program} {m : Mir.Program} :
    checkDocuments ct mt = .ok (c, m) ↔
      readCore ct = .ok c ∧ readMir mt = .ok m ∧
      WellFormedProgram c ∧ m.WellFormed ∧ Pair.Canonical c m := by
  unfold checkDocuments
  cases hc : readCore ct with
  | error e => simp [bind, Except.bind]
  | ok cp =>
    cases hm : readMir mt with
    | error e => simp [bind, Except.bind]
    | ok mp =>
      simp only [bind, Except.bind]
      split
      · rename_i hp
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl, (Pair.check_iff _ _).mp hp⟩
        · intro h; exact ⟨h.1, h.2.1⟩
      · rename_i hp
        constructor
        · intro h; cases h
        · rintro ⟨h1, h2, hv⟩
          cases h1; cases h2
          exact False.elim (hp ((Pair.check_iff c m).mpr hv))

/-- This is a conditional acceptance theorem, not a proof of the byte parser. -/
theorem accepted_documents {ct mt : String} {c : Program} {m : Mir.Program}
    (h : checkDocuments ct mt = .ok (c, m)) :
    WellFormedProgram c ∧ m.WellFormed ∧ Pair.Canonical c m :=
  checkDocuments_iff.mp h |>.2.2

end ANL.Memory.Wire
