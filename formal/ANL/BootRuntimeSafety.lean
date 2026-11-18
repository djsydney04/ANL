import ANL.BootRuntimeHistoryPreservation

namespace ANL.Boot.Runtime
variable {p : ANL.Boot.Program} {s : State}

/-- Independent current-state invariants; no runner, future outcome or reachability premise is a field. -/
structure SafetyInvariant (p : Program) (env : Environment) (s : State) : Prop where
  localSafety : LocalSafety p env s
  handler : HandlerOrbit p s
  history : StateHistory p env s

inductive BootStepsN (p : Program) (env : Environment) : Nat → State → State → Prop where
  | zero : BootStepsN p env 0 state state
  | succ : BootStep p env first middle → BootStepsN p env n middle last → BootStepsN p env (n + 1) first last

 theorem Start.safety (wf : WellFormedProgram p) (input : InputValid p env) (started : Start p env s) :
    SafetyInvariant p env s := ⟨started.localSafety wf input, started.handler_orbit, started.history⟩

 theorem BootStep.safety (wf : WellFormedProgram p) (input : InputValid p env)
    (old : SafetyInvariant p env s) (step : BootStep p env s next) : SafetyInvariant p env next :=
  ⟨step.localSafety wf old.localSafety, step.handler_orbit wf old.localSafety old.handler,
    step.history wf input old.localSafety old.handler old.history⟩

 theorem BootStepsN.safety (wf : WellFormedProgram p) (input : InputValid p env)
    (old : SafetyInvariant p env s) (steps : BootStepsN p env n s last) : SafetyInvariant p env last := by
  induction steps with
  | zero => exact old
  | succ step _ ih => exact ih (step.safety wf input old)

 theorem checked_entry_safety (wf : WellFormedProgram p) (input : InputValid p env) (started : Start p env first)
    (steps : BootStepsN p env n first last) : SafetyInvariant p env last := steps.safety wf input (started.safety wf input)

 theorem BootStepsN.append (left : BootStepsN p env n s middle) (right : BootStepsN p env m middle last) :
    BootStepsN p env (n + m) s last := by
  induction left with
  | zero => simpa using right
  | succ step _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using BootStepsN.succ step (ih right)

 theorem BootStepsN.deterministic (left : BootStepsN p env n s last) (right : BootStepsN p env n s other) : last = other := by
  induction left generalizing other with
  | zero => cases right; rfl
  | succ step _ ih =>
    cases right with | succ step' rest' =>
     have same := step.deterministic step'
     subst same
     exact ih rest'

 theorem outcome_blocked_retains (outcome : BootOutcome p env s (.blockedRead next)) : next = s := by
  exact outcome.blocked.1

 theorem outcome_ineligible_retains (outcome : BootOutcome p env s (.ineligibleDelivery next)) : next = s := by
  cases outcome with | ready _ execution =>
   cases execution <;> rename_i cut
   all_goals cases cut; rfl

 theorem safety_progress (wf : WellFormedProgram p) (input : InputValid p env) (safe : SafetyInvariant p env s) :
    (∃ next, tickRaw p env s = .advance next ∧ SafetyInvariant p env next) ∨
    tickRaw p env s = .blockedRead s ∨ tickRaw p env s = .ineligibleDelivery s := by
  cases actual : tickRaw p env s with
  | advance next => exact .inl ⟨next, rfl, (tickRaw_step_iff.mp actual).safety wf input safe⟩
  | blockedRead next =>
    have retained := outcome_blocked_retains (tickRaw_iff.mp actual)
    subst next
    exact .inr (.inl rfl)
  | ineligibleDelivery next =>
    have retained := outcome_ineligible_retains (tickRaw_iff.mp actual)
    subst next
    exact .inr (.inr rfl)
  | invalidState next => exact False.elim ((local_not_invalidState wf input safe.localSafety) actual)

 theorem checked_entry_progress (wf : WellFormedProgram p) (input : InputValid p env) (started : Start p env first)
    (steps : BootStepsN p env n first last) :
    (∃ next, tickRaw p env last = .advance next ∧ SafetyInvariant p env next) ∨
    tickRaw p env last = .blockedRead last ∨ tickRaw p env last = .ineligibleDelivery last :=
  safety_progress wf input (checked_entry_safety wf input started steps)

end ANL.Boot.Runtime
