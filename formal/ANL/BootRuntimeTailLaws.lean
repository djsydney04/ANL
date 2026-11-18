import ANL.BootRuntimeTailRun
import ANL.BootRuntimeHistoryCounts
import ANL.BootRuntimeObservationLaws

namespace ANL.Boot.Runtime
variable {p : Program} {s : State}

theorem runAccum_used (p : Program) (env : Environment) (budget : Nat) (s : State) (used : Nat) :
    (runAccum p env budget s used).used = (runRaw p env budget s).used + used := by
  rw [runAccum_eq]
  rfl

theorem runAccum_bound : used ≤ (runAccum p env budget s used).used ∧
    (runAccum p env budget s used).used ≤ used + budget := by
  rw [runAccum_used]
  have bound := runRaw_bound (p := p) (env := env) (budget := budget) (s := s)
  omega

theorem runTailRaw_iff : runTailRaw p env budget s = result ↔ RunTo p env budget s result := by
  rw [runTailRaw_eq, runRaw_iff]

theorem resumeTailRaw_iff : resumeTailRaw p env budget s = result ↔ ResumeTo p env budget s result := by
  rw [resumeTailRaw_eq, resumeRaw_iff]

theorem runTailRaw_prefix : BootStepsN p env (runTailRaw p env budget s).used s
    (runTailRaw p env budget s).state := by
  simpa only [runTailRaw_eq] using runRaw_prefix (p := p) (env := env) (budget := budget) (s := s)

theorem resumeTailRaw_prefix : BootStepsN p env (resumeTailRaw p env budget s).used s
    (resumeTailRaw p env budget s).state := by
  simpa only [resumeTailRaw_eq] using resumeRaw_prefix (p := p) (env := env) (budget := budget) (s := s)

theorem runTailRaw_bound : (runTailRaw p env budget s).used ≤ budget := by
  rw [runTailRaw_eq]
  exact runRaw_bound

theorem resumeTailRaw_bound : (resumeTailRaw p env budget s).used ≤ budget := by
  rw [resumeTailRaw_eq]
  exact resumeRaw_bound

theorem runTailRaw_zero_absent (absent : ∀ kind, ¬ Observation p s kind) :
    runTailRaw p env 0 s = ⟨.exhausted, s, 0⟩ := by
  rw [runTailRaw_eq]
  exact run_zero_unobserved_frontier absent

theorem runTailRaw_observed (observed : Observation p s kind) :
    runTailRaw p env budget s = observationResult env s kind := by
  simp [runTailRaw_eq, runRaw.eq_def, observed.compute]

theorem resumeTailRaw_zero : resumeTailRaw p env 0 s = ⟨.exhausted, s, 0⟩ := rfl

theorem resumeTailRaw_advance (step : BootStep p env s next) :
    resumeTailRaw p env (budget + 1) s = (runTailRaw p env budget next).bump := by
  rw [resumeTailRaw_eq, runTailRaw_eq]
  exact (ResumeTo.advance step runRaw_sound).compute

theorem runTailRaw_safety (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : SafetyInvariant p env s) :
    SafetyInvariant p env (runTailRaw p env budget s).state ∧
      (runTailRaw p env budget s).reason ≠ .invalidState := by
  rw [runTailRaw_eq]
  exact ⟨runRaw_sound.safety wf input safe, runRaw_sound.not_invalid wf input safe⟩

theorem resumeTailRaw_safety (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : SafetyInvariant p env s) :
    SafetyInvariant p env (resumeTailRaw p env budget s).state ∧
      (resumeTailRaw p env budget s).reason ≠ .invalidState := by
  rw [resumeTailRaw_eq]
  exact ⟨resumeRaw_sound.safety wf input safe, resumeRaw_sound.not_invalid wf input safe⟩

theorem runTailRaw_event_offsets (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : SafetyInvariant p env s) :
    ∃ added, (runTailRaw p env budget s).state.events = s.events ++ added ∧
      (runTailRaw p env budget s).state.eventCount = s.eventCount + added.length ∧
      (runTailRaw p env budget s).state.events.drop s.eventCount = added ∧
      added.length ≤ (runTailRaw p env budget s).used :=
  runTailRaw_prefix.event_offsets safe.history (runTailRaw_safety wf input safe).1.history

theorem resumeTailRaw_event_offsets (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : SafetyInvariant p env s) :
    ∃ added, (resumeTailRaw p env budget s).state.events = s.events ++ added ∧
      (resumeTailRaw p env budget s).state.eventCount = s.eventCount + added.length ∧
      (resumeTailRaw p env budget s).state.events.drop s.eventCount = added ∧
      added.length ≤ (resumeTailRaw p env budget s).used :=
  resumeTailRaw_prefix.event_offsets safe.history (resumeTailRaw_safety wf input safe).1.history

theorem runTailRaw_checked_event_count (wf : WellFormedProgram p) (input : InputValid p env)
    (started : Start p env s) :
    (runTailRaw p env budget s).state.eventCount = (runTailRaw p env budget s).state.events.length ∧
      (runTailRaw p env budget s).state.eventCount ≤ budget := by
  obtain ⟨count, bound⟩ := checked_prefix_event_count wf input started runTailRaw_prefix
  exact ⟨count, Nat.le_trans bound runTailRaw_bound⟩

theorem SelectedSpin.runTailRaw_exhausted (spin : SelectedSpin p s) :
    (runTailRaw p env budget s).reason = .exhausted ∧ (runTailRaw p env budget s).used = budget := by
  rw [runTailRaw_eq]
  exact spin.run_exhausted

theorem resumeTailRaw_park_exhausted (phase : s.phase = .parkObserved location)
    (valid : ParkConsumed p s location) :
    (resumeTailRaw p env (budget + 1) s).reason = .exhausted ∧
      (resumeTailRaw p env (budget + 1) s).used = budget + 1 := by
  rw [resumeTailRaw_eq]
  exact resume_park_exhausted phase valid

end ANL.Boot.Runtime
