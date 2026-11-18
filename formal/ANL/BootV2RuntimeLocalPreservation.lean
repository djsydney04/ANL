import ANL.BootV2RuntimeInterceptionSafety

namespace ANL.Boot.V2.Runtime
variable {p : ANL.Boot.V2.Program} {env : Environment} {s : State}

theorem Cut.coherent (wf : WellFormedProgram p) (old : Coherent p env s)
    (fallbackCoherent : Coherent p env fallback)
    (cut : Cut p env s key fallback (.advance next)) : Coherent p env next := by
  cases cut with
  | absent => exact fallbackCoherent
  | deliver _ _ reset => exact reset.coherent wf old

/-- Preservation uses actual Ready and Execute, never a history or reachability premise. -/
theorem BootStep.coherent (wf : WellFormedProgram p) (input : InputValid p env)
    (old : Coherent p env s) (step : BootStep p env s next) : Coherent p env next := by
  cases step with | advance ready execution =>
   cases execution with
   | language reset => exact reset.coherent wf old
   | enterPark => cases ready with | park _ first => exact park_waiting_coherent old first
   | capturedLegacy => cases ready with | captureLegacy _ _ captured => exact captured_legacy_coherent old captured
   | capturedFault => cases ready with | captureFault _ _ _ captured => exact captured_fault_coherent old captured
   | ordinary step =>
     cases ready with | ordinary phase _ _ _ _ => exact ordinary_local_coherent wf old phase step
   | legacyBefore cut =>
     cases ready with | legacyBefore _ valid => exact cut.coherent wf old (legacy_before_coherent old valid)
   | legacyCommit effect =>
     cases ready with | legacyCommit _ valid => exact legacy_commit_coherent old valid effect
   | legacyAfter cut =>
     cases ready with | legacyAfter phase valid => exact cut.coherent wf old (legacy_after_coherent old phase valid)
   | legacyFinish =>
     cases ready with | legacyFinish _ valid => exact legacy_return_coherent wf old valid
   | parkBoot _ cut =>
     cases ready with | parkCheck _ waiting => exact cut.coherent wf old (observed_park_coherent old waiting)
   | parkHandler => cases ready with | parkCheck _ waiting => exact observed_park_coherent old waiting
   | parkResume => exact with_phase_coherent old (.ordinary rfl)
   | faultBefore cut =>
     cases ready with | faultBefore _ valid => exact cut.coherent wf old (fault_before_coherent old valid)
   | raised raised => exact raised.coherent old
   | forwarded reset => exact reset.coherent wf input old

theorem ready_execute_coherent (wf : WellFormedProgram p) (input : InputValid p env)
    (old : Coherent p env s) (ready : Ready p env s cmd) (execution : Execute p env s cmd result) :
    Coherent p env result.state := by
  cases result with
  | advance next => exact (BootStep.advance ready execution).coherent wf input old
  | blockedRead next | blockedForwarding next | ineligibleDelivery next | invalidState next =>
    have same : next = s := execution.stopped (by intro candidate eq; cases eq)
    simpa [TickResult.state, same] using old

theorem BootOutcome.coherent (wf : WellFormedProgram p) (input : InputValid p env)
    (old : Coherent p env s) (outcome : BootOutcome p env s result) : Coherent p env result.state := by
  cases outcome with
  | ready ready execution => exact ready_execute_coherent wf input old ready execution
  | invalid => exact old

theorem tick_preserves_coherence (wf : WellFormedProgram p) (input : ValidatedInput p)
    (old : Coherent p input.raw s) : Coherent p input.raw (tick p input s).state :=
  (tickRaw_sound (p := p) (env := input.raw) (s := s)).coherent wf input.valid old

/-- The only alternative to retention is the actual current snapshot, without counting resets. -/
theorem BootStep.snapshot_update (step : BootStep p env s next) :
    next.interrupted = s.interrupted ∨ next.interrupted = some s.snapshot := by
  cases step with | advance _ execution =>
   cases execution with
   | language reset =>
     right
     cases reset
     rfl
   | enterPark | capturedLegacy | capturedFault | ordinary | legacyCommit | legacyFinish | parkHandler | parkResume =>
     exact .inl rfl
   | legacyBefore cut | legacyAfter cut | parkBoot _ cut | faultBefore cut =>
     cases cut with
     | absent => exact .inl rfl
     | deliver _ _ reset =>
       right
       cases reset
       rfl
   | raised raised =>
     left
     cases raised
     rfl
   | forwarded reset => exact .inr reset.saved_pending.1

/-- Finite reachability is a conclusion domain; local preservation does not assume it. -/
inductive Reachable (p : Program) (env : Environment) : State → Prop where
  | start {s : State} : Start p env s → Reachable p env s
  | step {s next : State} : Reachable p env s → BootStep p env s next → Reachable p env next

theorem Reachable.coherent (wf : WellFormedProgram p) (input : InputValid p env)
    (reached : Reachable p env s) : Coherent p env s := by
  induction reached with
  | start started => exact started.coherent wf input
  | step _ actual ih => exact actual.coherent wf input ih

end ANL.Boot.V2.Runtime
