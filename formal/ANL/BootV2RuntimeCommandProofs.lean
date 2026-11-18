import ANL.BootV2RuntimeCommands

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (NonTrap languageTag languageTag_iff)
variable {p : ANL.Boot.V2.Program} {env : Environment} {s : State}
set_option linter.unusedSimpArgs false

theorem option_none_iff {value : Option α} : value = none ↔ ∀ x, value ≠ some x := by
  cases value <;> simp

theorem captureLegacy_none_iff : captureLegacy p s = none ↔ ∀ q, ¬ CapturedLegacy p s q := by
  simp only [← captureLegacy_iff]
  exact option_none_iff

theorem captureFault_none_iff : captureFault p env s = none ↔ ∀ q, ¬ CapturedFault p env s q := by
  simp only [← captureFault_iff]
  exact option_none_iff

theorem command_sound (found : command p env s = some cmd) : Ready p env s cmd := by
  cases phaseEq : s.phase with
  | legacy phase =>
    cases phase with
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
            exact .captureLegacy phaseEq notFirst (captureLegacy_iff.mp captured)
          next noLegacy =>
            split at found
            next q captured =>
              simp only [Option.some.injEq] at found
              subst cmd
              exact .captureFault phaseEq notFirst (captureLegacy_none_iff.mp noLegacy)
                (captureFault_iff.mp captured)
            next noFault =>
              simp only [Option.some.injEq] at found
              subst cmd
              exact .ordinary phaseEq nontrap notFirst (captureLegacy_none_iff.mp noLegacy)
                (captureFault_none_iff.mp noFault)
    | primitiveBefore q | primitiveCommit q | primitiveAfter q value | primitiveReturn q value
    | parkCheck location | parkObserved location =>
      simp only [command, phaseEq] at found
      split at found
      next valid =>
        simp only [Option.some.injEq] at found
        subst cmd
        first
        | exact .legacyBefore phaseEq valid
        | exact .legacyCommit phaseEq valid
        | exact .legacyAfter phaseEq valid
        | exact .legacyFinish phaseEq valid
        | exact .parkCheck phaseEq valid
        | exact .parkResume phaseEq valid
      next => cases found
  | faultBefore q | faultCommit q | faultPending q =>
    simp only [command, phaseEq] at found
    split at found
    next valid =>
      simp only [Option.some.injEq] at found
      subst cmd
      first
      | exact .faultBefore phaseEq valid
      | exact .faultCommit phaseEq valid
      | exact .faultPending phaseEq valid
    next => cases found

theorem Ready.compute (ready : Ready p env s cmd) : command p env s = some cmd := by
  cases ready with
  | language phaseEq controlEq tag => simp [command, phaseEq, controlEq, languageTag_iff.mpr tag]
  | park phaseEq first => simp [command, phaseEq, first.1.exact.1, first]
  | captureLegacy phaseEq notFirst captured =>
    have cap := captureLegacy_iff.mpr captured
    cases captured with
    | invoke controlEq _ _ _ => simp [command, phaseEq, controlEq, notFirst, cap]
  | captureFault phaseEq notFirst noLegacy captured =>
    obtain ⟨controlEq, _, _⟩ := captured.valid.1.invocation
    simp [command, phaseEq, controlEq, notFirst, captureLegacy_none_iff.mpr noLegacy,
      captureFault_iff.mpr captured]
  | ordinary phaseEq nontrap notFirst noLegacy noFault =>
    cases controlEq : s.machine.control <;>
      simp_all [command, NonTrap, captureLegacy_none_iff.mpr noLegacy, captureFault_none_iff.mpr noFault]
  | legacyBefore phaseEq valid | legacyCommit phaseEq valid | legacyAfter phaseEq valid
  | legacyFinish phaseEq valid | parkCheck phaseEq valid | parkResume phaseEq valid
  | faultBefore phaseEq valid | faultCommit phaseEq valid | faultPending phaseEq valid =>
    simp [command, phaseEq, valid]

theorem command_iff : command p env s = some cmd ↔ Ready p env s cmd := ⟨command_sound, Ready.compute⟩

theorem Ready.unique (a : Ready p env s x) (b : Ready p env s y) : x = y :=
  Option.some.inj (a.compute.symm.trans b.compute)

theorem command_none_iff : command p env s = none ↔ ∀ cmd, ¬ Ready p env s cmd := by
  simp only [← command_iff]
  exact option_none_iff

theorem hardwareReset_none_iff : resetHardware p s d = none ↔ ∀ next, ¬ HardwareReset p s d next := by
  simp only [← resetHardware_iff]
  exact option_none_iff

theorem Cut.compute (meaning : Cut p env s key fallback result) : atCut p env s key fallback = result := by
  cases meaning with
  | absent absent => simp [atCut, deliveryAt_none_iff.mpr absent]
  | ineligible present ineligible => simp [atCut, deliveryAt_iff.mpr present, ineligible]
  | deliver present eligible reset => simp [atCut, deliveryAt_iff.mpr present, eligible, resetHardware_iff.mpr reset]
  | invalid present eligible absent => simp [atCut, deliveryAt_iff.mpr present, eligible, hardwareReset_none_iff.mpr absent]

theorem atCut_sound : Cut p env s key fallback (atCut p env s key fallback) := by
  unfold atCut
  split
  next absent => exact .absent (deliveryAt_none_iff.mp absent)
  next d present =>
    split
    next eligible =>
      split
      next next reset => exact .deliver (deliveryAt_iff.mp present) eligible (resetHardware_iff.mp reset)
      next absent => exact .invalid (deliveryAt_iff.mp present) eligible (hardwareReset_none_iff.mp absent)
    next ineligible => exact .ineligible (deliveryAt_iff.mp present) ineligible

theorem atCut_iff : atCut p env s key fallback = result ↔ Cut p env s key fallback result := by
  constructor
  · intro eq; rw [← eq]; exact atCut_sound
  · exact Cut.compute

theorem Cut.deterministic (a : Cut p env s key fallback x) (b : Cut p env s key fallback y) : x = y :=
  a.compute.symm.trans b.compute

theorem Cut.stopped (cut : Cut p env s key fallback result)
    (stopped : ∀ next, result ≠ .advance next) : result.state = s := by
  cases cut with
  | absent => exact False.elim (stopped _ rfl)
  | deliver => exact False.elim (stopped _ rfl)
  | ineligible | invalid => rfl

end ANL.Boot.V2.Runtime
