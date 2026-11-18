import ANL.BootRuntimeTick
import ANL.BootRuntimeCommandProofs

namespace ANL.Boot.Runtime
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem option_none_iff {value : Option α} : value = none ↔ ∀ x, value ≠ some x := by
  cases value <;> simp

 theorem hardwareReset_none_iff : resetHardware p s d = none ↔ ∀ next, ¬ HardwareReset p s d next := by
  simp only [← resetHardware_iff]
  exact option_none_iff
 theorem languageReset_none_iff : resetLanguage p s tag = none ↔ ∀ next, ¬ LanguageReset p s tag next := by
  simp only [← resetLanguage_iff]
  exact option_none_iff
 theorem perform_none_iff : perform p env h cursor op args = none ↔ ∀ result, ¬ Effect p env h cursor op args result := by
  simp only [← perform_iff]
  exact option_none_iff
 theorem originStep_none_iff {s : State} : Origin.step p noAllocations s.machine s.origins = none ↔
    ∀ next origins, ¬ Origin.Step p noAllocations s.machine s.origins next origins := by
  simp only [← Origin.step_iff, option_none_iff]
  exact ⟨fun absent next origins => absent (next, origins), fun absent ⟨next, origins⟩ => absent next origins⟩

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

 theorem Execute.compute (meaning : Execute p env s cmd result) : execute p env s cmd = result := by
  cases meaning with
  | language reset => simp [execute, resetLanguage_iff.mpr reset]
  | languageInvalid absent => simp [execute, languageReset_none_iff.mpr absent]
  | enterPark | captured | finish | parkResume => rfl
  | ordinary step => simp [execute, Origin.step_iff.mpr step]
  | ordinaryInvalid absent => simp [execute, originStep_none_iff.mpr absent]
  | before cut | after cut => exact cut.compute
  | commit effect => simp [execute, perform_iff.mpr effect]
  | blocked block => simp [execute, block.perform_none, block]
  | commitInvalid absent unblocked => simp [execute, perform_none_iff.mpr absent, unblocked]
  | parkBoot boot cut => simp [execute, boot, cut.compute]
  | parkHandler handler => simp [execute, handler]

 theorem execute_sound : Execute p env s cmd (execute p env s cmd) := by
  cases cmd with
  | language tag =>
    simp only [execute]
    split
    next next reset => exact .language (resetLanguage_iff.mp reset)
    next absent => exact .languageInvalid (languageReset_none_iff.mp absent)
  | enterPark => exact .enterPark
  | captured => exact .captured
  | ordinary =>
    simp only [execute]
    split
    next next origins step => exact .ordinary (Origin.step_iff.mp step)
    next absent => exact .ordinaryInvalid (originStep_none_iff.mp absent)
  | before => exact .before atCut_sound
  | commit q =>
    simp only [execute]
    split
    next result effect => exact .commit (perform_iff.mp effect)
    next absent =>
      split
      next block => exact .blocked block
      next unblocked => exact .commitInvalid (perform_none_iff.mp absent) unblocked
  | after => exact .after atCut_sound
  | finish => exact .finish
  | parkCheck location =>
    simp only [execute]
    split
    next boot => exact .parkBoot boot atCut_sound
    next handler => exact .parkHandler handler
  | parkResume => exact .parkResume

 theorem execute_iff : execute p env s cmd = result ↔ Execute p env s cmd result := by
  constructor
  · intro eq; rw [← eq]; exact execute_sound
  · exact Execute.compute

 theorem BootOutcome.compute (meaning : BootOutcome p env s result) : tickRaw p env s = result := by
  cases meaning with
  | ready ready execution => simp [tickRaw, ready.compute, execution.compute]
  | invalid absent => simp [tickRaw, command_none_iff.mpr absent]

 theorem tickRaw_sound : BootOutcome p env s (tickRaw p env s) := by
  unfold tickRaw
  split
  next cmd ready => exact .ready (command_iff.mp ready) execute_sound
  next absent => exact .invalid (command_none_iff.mp absent)

 theorem tickRaw_iff : tickRaw p env s = result ↔ BootOutcome p env s result := by
  constructor
  · intro eq; rw [← eq]; exact tickRaw_sound
  · exact BootOutcome.compute

/-- Agreement is even true for raw inputs; validation excludes malformed external data at the API gateway. -/
 theorem tick_iff : tick p input s = result ↔ BootOutcome p input.raw s result := tickRaw_iff

 theorem tickRaw_step_iff : tickRaw p env s = .advance next ↔ BootStep p env s next := by
  rw [tickRaw_iff]
  constructor
  · intro outcome
    cases outcome with | ready ready execution => exact .advance ready execution
  · intro step
    cases step with | advance ready execution => exact .ready ready execution

 theorem tick_step_iff : tick p input s = .advance next ↔ BootStep p input.raw s next := tickRaw_step_iff

 theorem BootOutcome.deterministic (a : BootOutcome p env s x) (b : BootOutcome p env s y) : x = y :=
  a.compute.symm.trans b.compute
 theorem BootStep.deterministic (a : BootStep p env s x) (b : BootStep p env s y) : x = y := by
  have eq := (tickRaw_step_iff.mpr a).symm.trans (tickRaw_step_iff.mpr b)
  cases eq
  rfl

end ANL.Boot.Runtime
