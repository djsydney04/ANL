import ANL.BootV2RuntimeTick
import ANL.BootV2RuntimeCommandProofs

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (wordValue_iff noAllocations)
variable {p : ANL.Boot.V2.Program} {env : Environment} {s : State}
set_option linter.unusedSimpArgs false

theorem languageReset_none_iff : resetLanguage p s tag = none ↔ ∀ next, ¬ LanguageReset p s tag next := by
  simp only [← resetLanguage_iff]
  exact option_none_iff

theorem performLegacy_none_iff : performLegacy p env h cursor op args = none ↔
    ∀ result, ¬ LegacyEffect p env h cursor op args result := by
  simp only [← performLegacy_iff]
  exact option_none_iff

theorem originStep_none_iff : Origin.step p noAllocations s.machine s.origins = none ↔
    ∀ next origins, ¬ Origin.Step p noAllocations s.machine s.origins next origins := by
  simp only [← Origin.step_iff, option_none_iff]
  exact ⟨fun absent next origins => absent (next, origins), fun absent ⟨next, origins⟩ => absent next origins⟩

theorem raiseFault_iff : raiseFault p env s q = some next ↔ Raised p env s q next := by
  constructor
  · intro found
    unfold raiseFault at found
    split at found
    next valid =>
      simp only [Option.some.injEq] at found
      subst next
      exact .raise valid.1 valid.2
    next => cases found
  · intro raised
    cases raised with | raise phase valid => simp [raiseFault, phase, valid]

theorem raiseFault_none_iff : raiseFault p env s q = none ↔ ∀ next, ¬ Raised p env s q next := by
  simp only [← raiseFault_iff]
  exact option_none_iff

theorem resetForward_iff : resetForward p env s q = some next ↔ ForwardReset p env s q next := by
  constructor
  · intro found
    unfold resetForward at found
    split at found
    next valid =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
      rcases found with ⟨cause, hc, pc, hp, auxiliary, ha, machine, hm, rfl⟩
      exact .handler valid.1 valid.2.1 valid.2.2 (wordValue_iff.mp hc) (wordValue_iff.mp hp)
        (wordValue_iff.mp ha) (enter_iff.mp hm)
    next => cases found
  · intro reset
    cases reset with
    | handler phase valid response hc hp ha hm =>
      simp [resetForward, phase, valid, response, wordValue_iff.mpr hc, wordValue_iff.mpr hp,
        wordValue_iff.mpr ha, enter_iff.mpr hm]

theorem resetForward_none_iff : resetForward p env s q = none ↔ ∀ next, ¬ ForwardReset p env s q next := by
  simp only [← resetForward_iff]
  exact option_none_iff

theorem ForwardReset.not_blocked (reset : ForwardReset p env s q next) : ¬ ForwardBlocked p env s q := by
  intro blocked
  cases reset with
  | handler _ _ response _ _ _ _ =>
    have absent := blocked.2.2
    rw [response] at absent
    cases absent

theorem Raised.deterministic (a : Raised p env s q x) (b : Raised p env s q y) : x = y :=
  Option.some.inj ((raiseFault_iff.mpr a).symm.trans (raiseFault_iff.mpr b))

theorem ForwardReset.deterministic (a : ForwardReset p env s q x) (b : ForwardReset p env s q y) : x = y :=
  Option.some.inj ((resetForward_iff.mpr a).symm.trans (resetForward_iff.mpr b))

theorem Execute.compute (meaning : Execute p env s cmd result) : execute p env s cmd = result := by
  cases meaning with
  | language reset => simp [execute, resetLanguage_iff.mpr reset]
  | languageInvalid absent => simp [execute, languageReset_none_iff.mpr absent]
  | enterPark | capturedLegacy | capturedFault | legacyFinish | parkResume => rfl
  | ordinary step => simp [execute, Origin.step_iff.mpr step]
  | ordinaryInvalid absent => simp [execute, originStep_none_iff.mpr absent]
  | legacyBefore cut | legacyAfter cut | faultBefore cut => exact cut.compute
  | legacyCommit effect => simp [execute, performLegacy_iff.mpr effect]
  | blockedRead blocked => simp [execute, blocked.perform_none, blocked]
  | legacyInvalid absent unblocked => simp [execute, performLegacy_none_iff.mpr absent, unblocked]
  | parkBoot boot cut => simp [execute, boot, cut.compute]
  | parkHandler handler => simp [execute, handler]
  | raised raised => simp [execute, raiseFault_iff.mpr raised]
  | raiseInvalid absent => simp [execute, raiseFault_none_iff.mpr absent]
  | forwardBlocked blocked => simp [execute, blocked]
  | forwarded reset => simp [execute, reset.not_blocked, resetForward_iff.mpr reset]
  | forwardInvalid unblocked absent => simp [execute, unblocked, resetForward_none_iff.mpr absent]

theorem execute_sound : Execute p env s cmd (execute p env s cmd) := by
  cases cmd with
  | language tag =>
    simp only [execute]
    split
    next next reset => exact .language (resetLanguage_iff.mp reset)
    next absent => exact .languageInvalid (languageReset_none_iff.mp absent)
  | enterPark => exact .enterPark
  | capturedLegacy => exact .capturedLegacy
  | capturedFault => exact .capturedFault
  | ordinary =>
    simp only [execute]
    split
    next next origins step => exact .ordinary (Origin.step_iff.mp step)
    next absent => exact .ordinaryInvalid (originStep_none_iff.mp absent)
  | legacyBefore => exact .legacyBefore atCut_sound
  | legacyCommit q =>
    simp only [execute]
    split
    next result effect => exact .legacyCommit (performLegacy_iff.mp effect)
    next absent =>
      split
      next blocked => exact .blockedRead blocked
      next unblocked => exact .legacyInvalid (performLegacy_none_iff.mp absent) unblocked
  | legacyAfter => exact .legacyAfter atCut_sound
  | legacyFinish => exact .legacyFinish
  | parkCheck location =>
    simp only [execute]
    split
    next boot => exact .parkBoot boot atCut_sound
    next handler => exact .parkHandler handler
  | parkResume => exact .parkResume
  | faultBefore => exact .faultBefore atCut_sound
  | faultCommit q =>
    simp only [execute]
    split
    next next raised => exact .raised (raiseFault_iff.mp raised)
    next absent => exact .raiseInvalid (raiseFault_none_iff.mp absent)
  | faultPending q =>
    simp only [execute]
    split
    next blocked => exact .forwardBlocked blocked
    next unblocked =>
      split
      next next reset => exact .forwarded (resetForward_iff.mp reset)
      next absent => exact .forwardInvalid unblocked (resetForward_none_iff.mp absent)

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

theorem Execute.stopped (meaning : Execute p env s cmd result)
    (stopped : ∀ next, result ≠ .advance next) : result.state = s := by
  cases meaning <;> first
  | exact False.elim (stopped _ rfl)
  | rfl
  | exact Cut.stopped (by assumption) stopped

theorem BootOutcome.stopped (meaning : BootOutcome p env s result)
    (stopped : ∀ next, result ≠ .advance next) : result.state = s := by
  cases meaning with
  | ready _ execution => exact execution.stopped stopped
  | invalid => rfl

theorem tickRaw_stopped (stopped : ∀ next, tickRaw p env s ≠ .advance next) : (tickRaw p env s).state = s :=
  tickRaw_sound.stopped stopped

end ANL.Boot.V2.Runtime
