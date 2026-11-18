import ANL.BootRuntimeRun

namespace ANL.Boot.Runtime
variable {p : Program}

 theorem outcome_invalid_retains (outcome : BootOutcome p env s (.invalidState next)) : next = s := by
  cases outcome with
  | invalid => rfl
  | ready _ execution =>
    cases execution
    all_goals first | rfl | (rename_i cut; cases cut; rfl)

 theorem RunTo.compute (meaning : RunTo p env budget s result) : runRaw p env budget s = result := by
  induction meaning with
  | observed observed absent => simp [runRaw.eq_def, observed.compute, observationResult, absent]
  | unobserved observed pending => simp [runRaw.eq_def, observed.compute, observationResult, pending]
  | exhausted absent => simp [runRaw, observe_none_iff.mpr absent]
  | blocked absent outcome => simp [runRaw, observe_none_iff.mpr absent, outcome.compute]
  | ineligible absent outcome => simp [runRaw, observe_none_iff.mpr absent, outcome.compute]
  | invalid absent outcome => simp [runRaw, observe_none_iff.mpr absent, outcome.compute]
  | advance absent step _ ih => simp [runRaw, observe_none_iff.mpr absent, tickRaw_step_iff.mpr step, ih]

 theorem runRaw_sound : RunTo p env budget s (runRaw p env budget s) := by
  induction budget generalizing s with
  | zero =>
    rw [runRaw]
    cases found : observe p s with
    | some kind =>
      simp only [observationResult]
      split
      next pending => exact .unobserved (observe_iff.mp found) pending
      next absent => exact .observed (observe_iff.mp found) absent
    | none => exact .exhausted (observe_none_iff.mp found)
  | succ budget ih =>
    rw [runRaw]
    cases found : observe p s with
    | some kind =>
      simp only [observationResult]
      split
      next pending => exact .unobserved (observe_iff.mp found) pending
      next absent => exact .observed (observe_iff.mp found) absent
    | none =>
      cases actual : tickRaw p env s with
      | advance next => exact .advance (observe_none_iff.mp found) (tickRaw_step_iff.mp actual) ih
      | blockedRead next =>
        have retained := outcome_blocked_retains (tickRaw_iff.mp actual)
        subst next
        exact .blocked (observe_none_iff.mp found) (tickRaw_iff.mp actual)
      | ineligibleDelivery next =>
        have retained := outcome_ineligible_retains (tickRaw_iff.mp actual)
        subst next
        exact .ineligible (observe_none_iff.mp found) (tickRaw_iff.mp actual)
      | invalidState next =>
        have retained := outcome_invalid_retains (tickRaw_iff.mp actual)
        subst next
        exact .invalid (observe_none_iff.mp found) (tickRaw_iff.mp actual)

 theorem runRaw_iff : runRaw p env budget s = result ↔ RunTo p env budget s result := by
  constructor
  · intro eq; rw [← eq]; exact runRaw_sound
  · exact RunTo.compute

 theorem ResumeTo.compute (meaning : ResumeTo p env budget s result) : resumeRaw p env budget s = result := by
  cases meaning with
  | exhausted => rfl
  | blocked outcome => simp [resumeRaw, outcome.compute]
  | ineligible outcome => simp [resumeRaw, outcome.compute]
  | invalid outcome => simp [resumeRaw, outcome.compute]
  | advance step rest => simp [resumeRaw, tickRaw_step_iff.mpr step, rest.compute]

 theorem resumeRaw_sound : ResumeTo p env budget s (resumeRaw p env budget s) := by
  cases budget with
  | zero => exact .exhausted
  | succ budget =>
    rw [resumeRaw]
    cases actual : tickRaw p env s with
    | advance next => exact .advance (tickRaw_step_iff.mp actual) runRaw_sound
    | blockedRead next =>
      have retained := outcome_blocked_retains (tickRaw_iff.mp actual)
      subst next
      exact .blocked (tickRaw_iff.mp actual)
    | ineligibleDelivery next =>
      have retained := outcome_ineligible_retains (tickRaw_iff.mp actual)
      subst next
      exact .ineligible (tickRaw_iff.mp actual)
    | invalidState next =>
      have retained := outcome_invalid_retains (tickRaw_iff.mp actual)
      subst next
      exact .invalid (tickRaw_iff.mp actual)

 theorem resumeRaw_iff : resumeRaw p env budget s = result ↔ ResumeTo p env budget s result := by
  constructor
  · intro eq; rw [← eq]; exact resumeRaw_sound
  · exact ResumeTo.compute

 theorem run_iff : run p input budget s = result ↔ RunTo p input.raw budget s result := runRaw_iff
 theorem resumeObserved_iff : resumeObserved p input budget s observed = result ↔
    ResumeTo p input.raw budget s result := resumeRaw_iff

 theorem RunTo.deterministic (left : RunTo p env budget s a) (right : RunTo p env budget s b) : a = b :=
  left.compute.symm.trans right.compute
 theorem ResumeTo.deterministic (left : ResumeTo p env budget s a) (right : ResumeTo p env budget s b) : a = b :=
  left.compute.symm.trans right.compute

end ANL.Boot.Runtime
