import ANL.BootV3RuntimeCoherence
import ANL.BootV2RuntimeLocalPreservation

namespace ANL.Boot.V3.Runtime
variable {p : Program} {env : V2.Runtime.Environment} {s : V2.Runtime.State}

theorem cut_coherent (wf : WellFormedProgram p) (old : V2.Runtime.Coherent p env s)
    (fallbackCoherent : V2.Runtime.Coherent p env fallback)
    (cut : V2.Runtime.Cut p env s key fallback (.advance next)) : V2.Runtime.Coherent p env next := by
  cases cut with
  | absent => exact fallbackCoherent
  | deliver _ _ reset => exact hardware_reset_coherent wf old reset

/-- Preservation uses actual Ready and Execute, never a history or reachability premise. -/
theorem boot_step_coherent (wf : WellFormedProgram p) (old : V2.Runtime.Coherent p env s)
    (step : V2.Runtime.BootStep p env s next) : V2.Runtime.Coherent p env next := by
  cases step with | advance ready execution =>
    cases execution with
    | language reset => exact language_reset_coherent wf old reset
    | enterPark => cases ready with | park _ first => exact V2.Runtime.park_waiting_coherent old first
    | capturedLegacy =>
      cases ready with | captureLegacy _ _ captured => exact V2.Runtime.captured_legacy_coherent old captured
    | capturedFault =>
      cases ready with | captureFault _ _ _ captured => exact V2.Runtime.captured_fault_coherent old captured
    | ordinary step =>
      cases ready with | ordinary phase _ _ _ _ => exact ordinary_local_coherent wf old phase step
    | legacyBefore cut =>
      cases ready with | legacyBefore _ valid => exact cut_coherent wf old (V2.Runtime.legacy_before_coherent old valid) cut
    | legacyCommit effect =>
      cases ready with | legacyCommit _ valid => exact V2.Runtime.legacy_commit_coherent old valid effect
    | legacyAfter cut =>
      cases ready with | legacyAfter phase valid =>
        exact cut_coherent wf old (V2.Runtime.legacy_after_coherent old phase valid) cut
    | legacyFinish =>
      cases ready with | legacyFinish _ valid => exact legacy_return_coherent wf old valid
    | parkBoot _ cut =>
      cases ready with | parkCheck _ waiting => exact cut_coherent wf old (V2.Runtime.observed_park_coherent old waiting) cut
    | parkHandler => cases ready with | parkCheck _ waiting => exact V2.Runtime.observed_park_coherent old waiting
    | parkResume => exact V2.Runtime.with_phase_coherent old (.ordinary rfl)
    | faultBefore cut =>
      cases ready with | faultBefore _ valid => exact cut_coherent wf old (V2.Runtime.fault_before_coherent old valid) cut
    | raised raised => exact raised.coherent old
    | forwarded reset => exact forward_reset_coherent wf old reset

theorem ready_execute_coherent (wf : WellFormedProgram p) (old : V2.Runtime.Coherent p env s)
    (ready : V2.Runtime.Ready p env s cmd) (execution : V2.Runtime.Execute p env s cmd result) :
    V2.Runtime.Coherent p env result.state := by
  cases result with
  | advance next => exact boot_step_coherent wf old (V2.Runtime.BootStep.advance ready execution)
  | blockedRead next | blockedForwarding next | ineligibleDelivery next | invalidState next =>
    have same : next = s := execution.stopped (by intro candidate eq; cases eq)
    simpa [V2.Runtime.TickResult.state, same] using old

theorem boot_outcome_coherent (wf : WellFormedProgram p) (old : V2.Runtime.Coherent p env s)
    (outcome : V2.Runtime.BootOutcome p env s result) : V2.Runtime.Coherent p env result.state := by
  cases outcome with
  | ready ready execution => exact ready_execute_coherent wf old ready execution
  | invalid => exact old

theorem tick_preserves_coherence (wf : WellFormedProgram p) (input : V2.Runtime.ValidatedInput p)
    (old : V2.Runtime.Coherent p input.raw s) : V2.Runtime.Coherent p input.raw (V2.Runtime.tick p input s).state :=
  boot_outcome_coherent wf old (V2.Runtime.tickRaw_sound (p := p) (env := input.raw) (s := s))

theorem reachable_coherent (wf : WellFormedProgram p) (input : V2.Runtime.InputValid p env)
    (reached : V2.Runtime.Reachable p env s) : V2.Runtime.Coherent p env s := by
  induction reached with
  | start started => exact start_coherent wf input started
  | step _ actual ih => exact boot_step_coherent wf ih actual

end ANL.Boot.V3.Runtime
