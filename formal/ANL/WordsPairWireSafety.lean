import ANL.WordsPairWire

namespace ANL.Words.Wire

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


end ANL.Words.Wire
