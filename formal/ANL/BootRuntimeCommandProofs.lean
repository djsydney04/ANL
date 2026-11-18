import ANL.BootRuntimeCommands

namespace ANL.Boot.Runtime
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem capture_none_iff : capture p s = none ↔ ∀ q, ¬ Captured p s q := by
  constructor
  · intro absent q present; rw [capture_iff.mpr present] at absent; cases absent
  · intro absent
    cases found : capture p s with
    | none => rfl
    | some q => exact False.elim (absent q (capture_iff.mp found))

 theorem command_sound (found : command p s = some cmd) : Ready p s cmd := by
  cases phaseEq : s.phase with
  | ordinary =>
    simp only [command, phaseEq] at found
    split at found
    next trap controlEq =>
      cases tagEq : languageTag trap with
      | none => simp [tagEq] at found
      | some tag =>
        simp only [tagEq, Option.map_some, Option.some.injEq] at found
        subst cmd
        exact .language phaseEq controlEq (languageTag_iff.mp tagEq)
    next notTrap =>
      have nontrap : NonTrap s.machine.control := by
        cases c : s.machine.control <;> try trivial
        exact False.elim (notTrap _ c)
      split at found
      next first =>
        simp only [Option.some.injEq] at found
        subst cmd
        exact .park phaseEq first
      next notFirst =>
        split at found
        next q captured =>
          simp only [Option.some.injEq] at found
          subst cmd
          exact .capture phaseEq notFirst (capture_iff.mp captured)
        next absent =>
          simp only [Option.some.injEq] at found
          subst cmd
          exact .ordinary phaseEq nontrap notFirst (capture_none_iff.mp absent)
  | primitiveBefore q | primitiveCommit q | primitiveAfter q v | primitiveReturn q v
  | parkCheck location | parkObserved location =>
    simp only [command, phaseEq] at found
    split at found
    next valid =>
      simp only [Option.some.injEq] at found
      subst cmd
      first
      | exact .before phaseEq valid
      | exact .commit phaseEq valid
      | exact .after phaseEq valid
      | exact .finish phaseEq valid
      | exact .parkCheck phaseEq valid
      | exact .parkResume phaseEq valid
    next => cases found

 theorem Ready.compute (ready : Ready p s cmd) : command p s = some cmd := by
  cases ready with
  | language phaseEq controlEq tag => simp [command, phaseEq, controlEq, languageTag_iff.mpr tag]
  | park phaseEq first => simp [command, phaseEq, first.1.exact.1, first]
  | capture phaseEq notFirst captured =>
    have cap := capture_iff.mpr captured
    cases captured with | invoke controlEq _ _ => simp [command, phaseEq, controlEq, notFirst, cap]
  | ordinary phaseEq nontrap notFirst absent =>
    cases controlEq : s.machine.control <;>
      simp_all [command, NonTrap, capture_none_iff.mpr absent]
  | before phaseEq valid | commit phaseEq valid | after phaseEq valid | finish phaseEq valid
  | parkCheck phaseEq valid | parkResume phaseEq valid => simp [command, phaseEq, valid]

 theorem command_iff : command p s = some cmd ↔ Ready p s cmd := ⟨command_sound, Ready.compute⟩
 theorem Ready.unique (a : Ready p s x) (b : Ready p s y) : x = y :=
  Option.some.inj (a.compute.symm.trans b.compute)
 theorem command_none_iff : command p s = none ↔ ∀ cmd, ¬ Ready p s cmd := by
  constructor
  · intro absent cmd ready; rw [ready.compute] at absent; cases absent
  · intro absent
    cases found : command p s with
    | none => rfl
    | some cmd => exact False.elim (absent cmd (command_sound found))

end ANL.Boot.Runtime
