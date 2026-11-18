import ANL.BootRuntimeRunAgreement

namespace ANL.Boot.Runtime
variable {p : Program}

inductive StopAt (p : Program) (env : Environment) (s : State) : StopReason → Prop where
  | observed : Observation p s kind → ¬ PendingDelivery env s → StopAt p env s (.observed kind)
  | unobserved : Observation p s kind → PendingDelivery env s → StopAt p env s (.unobserved kind)
  | blocked : (∀ kind, ¬ Observation p s kind) → BootOutcome p env s (.blockedRead s) → StopAt p env s .blockedRead
  | ineligible : (∀ kind, ¬ Observation p s kind) → BootOutcome p env s (.ineligibleDelivery s) → StopAt p env s .ineligibleDelivery
  | invalid : (∀ kind, ¬ Observation p s kind) → BootOutcome p env s (.invalidState s) → StopAt p env s .invalidState
  | exhausted : (∀ kind, ¬ Observation p s kind) → StopAt p env s .exhausted

 theorem RunTo.prefix (meaning : RunTo p env budget s result) : BootStepsN p env result.used s result.state := by
  induction meaning with
  | advance _ step _ ih => exact .succ step ih
  | _ => exact .zero

 theorem RunTo.bound (meaning : RunTo p env budget s result) : result.used ≤ budget := by
  induction meaning with
  | advance _ _ _ ih => exact Nat.succ_le_succ ih
  | _ => exact Nat.zero_le _

 theorem RunTo.stop (meaning : RunTo p env budget s result) : StopAt p env result.state result.reason := by
  induction meaning with
  | observed observed pending => exact .observed observed pending
  | unobserved observed pending => exact .unobserved observed pending
  | exhausted absent => exact .exhausted absent
  | blocked absent outcome => exact .blocked absent outcome
  | ineligible absent outcome => exact .ineligible absent outcome
  | invalid absent outcome => exact .invalid absent outcome
  | advance _ _ _ ih => exact ih

 theorem RunTo.exhausted_spec (meaning : RunTo p env budget s result) (stopped : result.reason = .exhausted) :
    result.used = budget ∧ ∀ kind, ¬ Observation p result.state kind := by
  induction meaning with
  | exhausted absent => exact ⟨rfl, absent⟩
  | advance _ _ _ ih =>
    obtain ⟨count, absent⟩ := ih stopped
    exact ⟨congrArg (· + 1) count, absent⟩
  | _ => contradiction

 theorem ResumeTo.prefix (meaning : ResumeTo p env budget s result) : BootStepsN p env result.used s result.state := by
  cases meaning with
  | advance step rest => exact .succ step rest.prefix
  | _ => exact .zero

 theorem ResumeTo.bound (meaning : ResumeTo p env budget s result) : result.used ≤ budget := by
  cases meaning with
  | advance _ rest => exact Nat.succ_le_succ rest.bound
  | _ => exact Nat.zero_le _

 theorem ResumeTo.exhausted_spec (meaning : ResumeTo p env budget s result) (stopped : result.reason = .exhausted) :
    result.used = budget ∧ (budget = 0 ∨ ∀ kind, ¬ Observation p result.state kind) := by
  cases meaning with
  | exhausted => exact ⟨rfl, .inl rfl⟩
  | advance _ rest =>
    obtain ⟨count, absent⟩ := rest.exhausted_spec stopped
    exact ⟨congrArg (· + 1) count, .inr absent⟩
  | _ => contradiction

 theorem runRaw_prefix : BootStepsN p env (runRaw p env budget s).used s (runRaw p env budget s).state :=
  runRaw_sound.prefix
 theorem runRaw_bound : (runRaw p env budget s).used ≤ budget := runRaw_sound.bound
 theorem runRaw_stop : StopAt p env (runRaw p env budget s).state (runRaw p env budget s).reason :=
  runRaw_sound.stop
 theorem resumeRaw_prefix : BootStepsN p env (resumeRaw p env budget s).used s (resumeRaw p env budget s).state :=
  resumeRaw_sound.prefix
 theorem resumeRaw_bound : (resumeRaw p env budget s).used ≤ budget := resumeRaw_sound.bound

 theorem RunTo.safety (wf : WellFormedProgram p) (input : InputValid p env) (safe : SafetyInvariant p env s)
    (meaning : RunTo p env budget s result) : SafetyInvariant p env result.state := meaning.prefix.safety wf input safe
 theorem ResumeTo.safety (wf : WellFormedProgram p) (input : InputValid p env) (safe : SafetyInvariant p env s)
    (meaning : ResumeTo p env budget s result) : SafetyInvariant p env result.state := meaning.prefix.safety wf input safe

 theorem RunTo.not_invalid (wf : WellFormedProgram p) (input : InputValid p env) (safe : SafetyInvariant p env s)
    (meaning : RunTo p env budget s result) : result.reason ≠ .invalidState := by
  intro invalid
  have safety := meaning.safety wf input safe
  have stopped := meaning.stop
  rw [invalid] at stopped
  cases stopped with | invalid _ outcome => exact (local_not_invalidState wf input safety.localSafety) outcome.compute

 theorem ResumeTo.not_invalid (wf : WellFormedProgram p) (input : InputValid p env) (safe : SafetyInvariant p env s)
    (meaning : ResumeTo p env budget s result) : result.reason ≠ .invalidState := by
  cases meaning with
  | exhausted | blocked | ineligible => intro impossible; contradiction
  | invalid outcome => exact False.elim ((local_not_invalidState wf input safe.localSafety) outcome.compute)
  | advance step rest => simpa only [RunResult.bump] using rest.not_invalid wf input (step.safety wf input safe)

 theorem run_checked_safety (wf : WellFormedProgram p) (input : ValidatedInput p) (started : Start p input.raw first) :
    SafetyInvariant p input.raw (run p input budget first).state ∧ (run p input budget first).reason ≠ .invalidState :=
  ⟨runRaw_sound.safety wf input.valid (started.safety wf input.valid),
   runRaw_sound.not_invalid wf input.valid (started.safety wf input.valid)⟩

 theorem run_event_prefix : ∃ added, (runRaw p env budget s).state.events = s.events ++ added ∧
    added.length ≤ (runRaw p env budget s).used := runRaw_prefix.ordered_event_prefix
 theorem resume_event_prefix : ∃ added, (resumeRaw p env budget s).state.events = s.events ++ added ∧
    added.length ≤ (resumeRaw p env budget s).used := resumeRaw_prefix.ordered_event_prefix

end ANL.Boot.Runtime
