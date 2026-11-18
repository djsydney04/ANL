import ANL.BootV3CheckProofs
import ANL.BootV2WireSafety

namespace ANL.Boot.V3.Wire

abbrev Decode := V2.Wire.Decode
abbrev core := V2.Wire.core
abbrev readCore := V2.Wire.readCore

def checkCoreDocument (text : String) : Decode Program := do
  let p ← readCore text
  if checkProgram p then return p
  else throw (V2.Wire.invalid "v3 boot Core static policy rejected")

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

theorem checked_not_v2 {text : String} {p q : Program}
    (checked : checkCoreDocument text = .ok p) :
    V2.Wire.checkCoreDocument text ≠ .ok q := by
  intro old
  obtain ⟨raw, valid⟩ := checkCoreDocument_iff.mp checked
  obtain ⟨oldRaw, oldValid⟩ := V2.Wire.checkCoreDocument_iff.mp old
  have same : p = q := Except.ok.inj (raw.symm.trans oldRaw)
  cases same
  exact valid.not_v2 oldValid

end ANL.Boot.V3.Wire
