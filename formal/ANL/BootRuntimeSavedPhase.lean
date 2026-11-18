import ANL.BootRuntimeSafety

namespace ANL.Boot.Runtime

/-- A saved phase comes from a phase-valid state, rather than a forged passive descriptor. -/
def SavedPhase (p : Program) (s : State) : Prop :=
  ∀ snapshot, s.interrupted = some snapshot →
    ∃ before, snapshot = before.snapshot ∧ PhaseInvariant p before

/-- Only actual reset rules replace the passive snapshot; every other advance retains it. -/
theorem BootStep.interrupted_cases (step : BootStep p env s next) :
    next.interrupted = s.interrupted ∨
      (∃ d, HardwareReset p s d next) ∨ (∃ tag, LanguageReset p s tag next) := by
  cases step with | advance ready execution =>
   cases execution with
   | language reset => exact .inr (.inr ⟨_, reset⟩)
   | before cut | after cut | parkBoot _ cut =>
     cases cut with
     | absent => exact .inl rfl
     | deliver _ _ reset => exact .inr (.inl ⟨_, reset⟩)
   | enterPark | captured | ordinary | commit | finish | parkHandler | parkResume => exact .inl rfl

theorem HardwareReset.interrupted (reset : HardwareReset p s d next) :
    next.interrupted = some s.snapshot := by cases reset; rfl

theorem LanguageReset.interrupted (reset : LanguageReset p s tag next) :
    next.interrupted = some s.snapshot := by cases reset; rfl

theorem Start.savedPhase (started : Start p env s) : SavedPhase p s := by
  cases started
  intro snapshot impossible
  contradiction

theorem BootStep.savedPhase (old : SavedPhase p s) (phase : PhaseInvariant p s)
    (step : BootStep p env s next) : SavedPhase p next := by
  intro snapshot retained
  rcases step.interrupted_cases with same | ⟨d, reset⟩ | ⟨tag, reset⟩
  · exact old snapshot (same ▸ retained)
  · exact ⟨s, Option.some.inj (retained.symm.trans reset.interrupted), phase⟩
  · exact ⟨s, Option.some.inj (retained.symm.trans reset.interrupted), phase⟩

theorem BootStepsN.savedPhase (wf : WellFormedProgram p) (old : RuntimeInvariant p env s)
    (saved : SavedPhase p s) (steps : BootStepsN p env n s last) : SavedPhase p last := by
  induction steps with
  | zero => exact saved
  | succ step _ ih => exact ih (step.invariant wf old) (step.savedPhase saved old.phase)

theorem checked_prefix_savedPhase (wf : WellFormedProgram p) (input : InputValid p env)
    (started : Start p env first) (steps : BootStepsN p env n first last) : SavedPhase p last :=
  steps.savedPhase wf (started.safety wf input).localSafety.runtime started.savedPhase


/-- The source witness belongs to this actual prefix and performs a reset on its next step. -/
theorem BootStepsN.interrupted_source (steps : BootStepsN p env n first last)
    (retained : last.interrupted = some snapshot) :
    first.interrupted = some snapshot ∨
      ∃ i before next j, BootStepsN p env i first before ∧
        BootStep p env before next ∧
        ((∃ d, HardwareReset p before d next) ∨ (∃ tag, LanguageReset p before tag next)) ∧
        snapshot = before.snapshot ∧ BootStepsN p env j next last ∧ n = i + 1 + j := by
  induction steps with
  | zero => exact .inl retained
  | @succ first middle n last step rest ih =>
    rcases ih retained with same | ⟨i, before, next, j, priorSteps, resetStep, reset, eq, suffix, count⟩
    · rcases step.interrupted_cases with unchanged | ⟨d, reset⟩ | ⟨tag, reset⟩
      · exact .inl (unchanged ▸ same)
      · exact .inr ⟨0, first, middle, n, .zero, step, .inl ⟨d, reset⟩,
          Option.some.inj (same.symm.trans reset.interrupted), rest, by omega⟩
      · exact .inr ⟨0, first, middle, n, .zero, step, .inr ⟨tag, reset⟩,
          Option.some.inj (same.symm.trans reset.interrupted), rest, by omega⟩
    · exact .inr ⟨i + 1, before, next, j, .succ step priorSteps, resetStep, reset, eq, suffix, by omega⟩

theorem checked_prefix_interrupted_source (wf : WellFormedProgram p) (input : InputValid p env)
    (started : Start p env first) (steps : BootStepsN p env n first last)
    (retained : last.interrupted = some snapshot) :
    ∃ i before next j, BootStepsN p env i first before ∧
      BootStep p env before next ∧
      ((∃ d, HardwareReset p before d next) ∨ (∃ tag, LanguageReset p before tag next)) ∧
      snapshot = before.snapshot ∧ PhaseInvariant p before ∧
      BootStepsN p env j next last ∧ n = i + 1 + j := by
  rcases steps.interrupted_source retained with old | ⟨i, before, next, j, priorSteps, step, reset, eq, suffix, count⟩
  · cases started
    contradiction
  · exact ⟨i, before, next, j, priorSteps, step, reset, eq,
      (checked_entry_safety wf input started priorSteps).localSafety.runtime.phase, suffix, count⟩

end ANL.Boot.Runtime
