import ANL.BootV2Wire
import ANL.BootV2CheckProofs

namespace ANL.Boot.V2.Wire

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

theorem checked_wellFormed {text : String} {p : Program}
    (checked : checkCoreDocument text = .ok p) : WellFormedProgram p :=
  (checkCoreDocument_iff.mp checked).2

end ANL.Boot.V2.Wire
