import ANL.BootV2RuntimeMachineSafety
import ANL.BootRuntimeInterceptionSafety

namespace ANL.Boot.V2.Runtime
open ANL.Words
variable {p : ANL.Boot.V2.Program} {env : Environment} {s : State}
set_option linter.unusedSimpArgs false

theorem with_phase_coherent (old : Coherent p env s)
    (phase : PhaseCoherent p env (withPhase s nextPhase)) : Coherent p env (withPhase s nextPhase) :=
  ⟨old.typed, old.aligned, old.memory, old.hardware, old.installed, old.stack, old.episode,
    phase, old.cursor, old.ordinal, old.bootSeen, old.passive⟩

theorem captured_legacy_coherent (old : Coherent p env s) (captured : CapturedLegacy p s q) :
    Coherent p env (withPhase s (.legacy (.primitiveBefore q))) :=
  with_phase_coherent old (.before rfl ⟨captured.valid, captured.ordinal⟩)

theorem captured_fault_coherent (old : Coherent p env s) (captured : CapturedFault p env s q) :
    Coherent p env (withPhase s (.faultBefore q)) :=
  with_phase_coherent old (.faultBefore rfl captured.valid)

theorem legacy_before_coherent (old : Coherent p env s) (valid : LegacyBeforeValid p s q) :
    Coherent p env (withPhase s (.legacy (.primitiveCommit q))) :=
  with_phase_coherent old (.commit rfl valid)

/-- Weak commit coherence preserves the accepted no-installation phase advance. -/
theorem fault_before_coherent (old : Coherent p env s) (valid : FaultBeforeValid p env s q) :
    Coherent p env (withPhase s (.faultCommit q)) :=
  with_phase_coherent old (.faultCommit rfl valid)

theorem legacy_after_coherent (old : Coherent p env s)
    (phase : s.phase = .legacy (.primitiveAfter q value)) (valid : LegacyAfterValid p s q value) :
    Coherent p env (withPhase s (.legacy (.primitiveReturn q value))) := by
  have latest : LatestLegacyCommit s q value := by
    cases old.phase <;> simp_all
  exact with_phase_coherent old (.finish rfl valid latest)

theorem park_waiting_coherent (old : Coherent p env s) (first : FirstPark p s) :
    Coherent p env (withPhase s (.legacy (.parkCheck s.origins.control))) :=
  with_phase_coherent old (.parkWaiting rfl first)

theorem observed_park_coherent (old : Coherent p env s) (waiting : ParkWaiting p s location) :
    Coherent p env (observedPark s location) := by
  refine ⟨old.typed, old.aligned, old.memory, old.hardware, old.installed, old.stack, old.episode,
    .parkConsumed rfl ?_, old.cursor, old.ordinal, ?_, old.passive⟩
  · exact ⟨waiting.1, rfl, by
      intro boot
      change s.episode = .boot at boot
      simp [observedPark, boot]⟩
  · intro boot _
    simp only [observedPark] at boot ⊢
    simp [boot]

theorem legacy_commit_coherent (old : Coherent p env s) (valid : LegacyBeforeValid p s q)
    (effect : LegacyEffect p env s.hardware s.readCursor q.operation q.arguments result) :
    Coherent p env (commitLegacyState s q result) := by
  refine ⟨old.typed, old.aligned, old.memory, effect.hardware_valid, effect.installed old.installed,
    old.stack, old.episode, ?_, effect.cursor_bound old.cursor, Nat.zero_lt_succ _, old.bootSeen, old.passive⟩
  apply PhaseCoherent.after rfl
  · exact ⟨valid.1, congrArg (fun n => n + 1) valid.2, effect.result_type⟩
  · exact ⟨result.payload, s.revEvents, rfl, ANL.Boot.Runtime.effect_payload effect.effect rfl rfl⟩

theorem legacy_return_coherent (wf : WellFormedProgram p) (old : Coherent p env s)
    (valid : LegacyAfterValid p s q value) : Coherent p env (returnLegacyState s value) :=
  ⟨returnLegacy_typed wf old.typed valid.1 valid.2.2, returnLegacy_aligned old.aligned valid.1,
    old.memory, old.hardware, old.installed, old.stack, old.episode, .ordinary rfl,
    old.cursor, old.ordinal, old.bootSeen, old.passive⟩

theorem Raised.coherent (old : Coherent p env s) (raised : Raised p env s q next) :
    Coherent p env next := by
  have pending := raised.pending_valid
  cases raised with
  | raise _ _ =>
    exact ⟨old.typed, old.aligned, old.memory, old.hardware, old.installed, old.stack, old.episode,
      .faultPending rfl pending, old.cursor, Nat.zero_lt_succ _, old.bootSeen, old.passive⟩

theorem ForwardReset.coherent (wf : WellFormedProgram p) (input : InputValid p env)
    (old : Coherent p env s) (reset : ForwardReset p env s q next) : Coherent p env next := by
  have typing := reset.typed wf input old.memory.1
  have hardware := reset.hardware_valid
  cases reset with | handler _ _ _ _ _ _ entered =>
   cases entered with | defined found =>
    refine ⟨typing.1, typing.2, ?_, hardware, old.installed, .hardware, .nil,
      .ordinary rfl, old.cursor, old.ordinal, ?_, ?_⟩
    · exact ⟨old.memory.1, rfl, by simp [forwardResetState]⟩
    · simp [forwardResetState]
    · intro snapshot eq
      simp only [forwardResetState, Option.some.injEq] at eq
      subst snapshot
      exact old.snapshot

end ANL.Boot.V2.Runtime
