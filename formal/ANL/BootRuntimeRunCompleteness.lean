import ANL.BootRuntimeRunBounds

namespace ANL.Boot.Runtime
variable {p : Program}

/-- Actual finite transitions before the first covered observation. A step itself excludes a block at that state. -/
inductive ObservationFreeStepsN (p : Program) (env : Environment) : Nat → State → State → Prop where
  | zero : ObservationFreeStepsN p env 0 state state
  | succ : (∀ kind, ¬ Observation p first kind) → BootStep p env first next →
      ObservationFreeStepsN p env n next last → ObservationFreeStepsN p env (n + 1) first last

 theorem ObservationFreeStepsN.steps (segment : ObservationFreeStepsN p env n s last) : BootStepsN p env n s last := by
  induction segment with
  | zero => exact .zero
  | succ _ step _ ih => exact .succ step ih

 theorem ObservationFreeStepsN.append (left : ObservationFreeStepsN p env n s middle)
    (right : ObservationFreeStepsN p env m middle last) : ObservationFreeStepsN p env (n + m) s last := by
  induction left with
  | zero => simpa using right
  | succ absent step _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ObservationFreeStepsN.succ absent step (ih right)

def RunResult.addUsed (result : RunResult) (n : Nat) : RunResult := { result with used := result.used + n }

 theorem ObservationFreeStepsN.prepend (segment : ObservationFreeStepsN p env n s last)
    (rest : RunTo p env budget last result) : RunTo p env (n + budget) s (result.addUsed n) := by
  induction segment with
  | zero => simpa [RunResult.addUsed] using rest
  | succ absent step _ ih =>
    have next := RunTo.advance absent step (ih rest)
    simpa [RunResult.addUsed, RunResult.bump, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

/-- Completeness applies to prefixes with no earlier observation; it never skips a stop. -/
 theorem runRaw_complete (segment : ObservationFreeStepsN p env n s last) :
    runRaw p env (n + budget) s = (runRaw p env budget last).addUsed n :=
  (segment.prepend runRaw_sound).compute

 theorem RunTo.exhausted_prefix (meaning : RunTo p env budget s result) (stopped : result.reason = .exhausted) :
    ObservationFreeStepsN p env budget s result.state := by
  induction meaning with
  | exhausted => exact .zero
  | advance absent step _ ih => exact .succ absent step (ih stopped)
  | _ => contradiction

 theorem runRaw_extend (stopped : (runRaw p env budget s).reason = .exhausted) :
    runRaw p env (budget + extra) s =
      (runRaw p env extra (runRaw p env budget s).state).addUsed budget :=
  runRaw_complete (runRaw_sound.exhausted_prefix stopped)

 theorem runRaw_observed_complete (segment : ObservationFreeStepsN p env n s last)
    (observed : Observation p last kind) (consumed : ¬ PendingDelivery env last) :
    runRaw p env (n + extra) s = ⟨.observed kind, last, n⟩ := by
  simpa [RunResult.addUsed] using (segment.prepend (RunTo.observed (budget := extra) observed consumed)).compute

 theorem runRaw_unobserved_complete (segment : ObservationFreeStepsN p env n s last)
    (observed : Observation p last kind) (pending : PendingDelivery env last) :
    runRaw p env (n + extra) s = ⟨.unobserved kind, last, n⟩ := by
  simpa [RunResult.addUsed] using (segment.prepend (RunTo.unobserved (budget := extra) observed pending)).compute

 theorem runRaw_blocked_complete (segment : ObservationFreeStepsN p env n s last)
    (absent : ∀ kind, ¬ Observation p last kind) (blocked : BootOutcome p env last (.blockedRead last)) :
    runRaw p env (n + (extra + 1)) s = ⟨.blockedRead, last, n⟩ := by
  simpa [RunResult.addUsed] using (segment.prepend (RunTo.blocked (budget := extra) absent blocked)).compute

 theorem runRaw_ineligible_complete (segment : ObservationFreeStepsN p env n s last)
    (absent : ∀ kind, ¬ Observation p last kind) (blocked : BootOutcome p env last (.ineligibleDelivery last)) :
    runRaw p env (n + (extra + 1)) s = ⟨.ineligibleDelivery, last, n⟩ := by
  simpa [RunResult.addUsed] using (segment.prepend (RunTo.ineligible (budget := extra) absent blocked)).compute

 theorem run_resume_prefix : BootStepsN p env
    ((runRaw p env firstBudget s).used + (resumeRaw p env nextBudget (runRaw p env firstBudget s).state).used)
    s (resumeRaw p env nextBudget (runRaw p env firstBudget s).state).state :=
  runRaw_prefix.append resumeRaw_prefix

 theorem resume_run_prefix : BootStepsN p env
    ((resumeRaw p env firstBudget s).used + (runRaw p env nextBudget (resumeRaw p env firstBudget s).state).used)
    s (runRaw p env nextBudget (resumeRaw p env firstBudget s).state).state :=
  resumeRaw_prefix.append runRaw_prefix

 theorem run_zero_unobserved_frontier (absent : ∀ kind, ¬ Observation p s kind) :
    runRaw p env 0 s = ⟨.exhausted, s, 0⟩ := (RunTo.exhausted absent).compute

 theorem run_zero_observed (observed : Observation p s kind) :
    runRaw p env 0 s = observationResult env s kind := by simp [runRaw, observed.compute]

 theorem resume_zero : resumeRaw p env 0 s = ⟨.exhausted, s, 0⟩ := rfl

end ANL.Boot.Runtime
