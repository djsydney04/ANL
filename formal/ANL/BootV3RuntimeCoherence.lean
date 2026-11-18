import ANL.BootV3RuntimeEntry
import ANL.BootOriginCarrierPreservation
import ANL.BootV2RuntimeInterceptionSafety

namespace ANL.Boot.V3.Runtime
open ANL.Words
variable {p : Program} {env : V2.Runtime.Environment} {s : V2.Runtime.State}
set_option linter.unusedSimpArgs false

theorem ordinary_local_coherent (wf : WellFormedProgram p) (old : V2.Runtime.Coherent p env s)
    (phase : s.phase = .legacy .ordinary)
    (step : V2.Origin.Step p responses s.machine s.origins machine origins) :
    V2.Runtime.Coherent p env (V2.Runtime.ordinaryState s machine origins) := by
  have typing := Words.preservation (carrier_wellFormed wf) old.typed step.erase
  have alignment := V2.Origin.preserve_carrier (carrier_wellFormed wf) old.typed old.aligned step
  have world : machine.world = .initial := by
    cases step with
    | ordinary admitted actual _ _ => exact (V2.Runtime.admitted_world admitted actual).trans old.memory.1
  exact ⟨typing, alignment, V2.Runtime.typed_aligned_memory typing alignment world,
    old.hardware, old.installed, old.stack, ANL.Boot.Runtime.step_episode old.episode step.erase,
    .ordinary phase, old.cursor, old.ordinal, old.bootSeen, old.passive⟩

theorem start_coherent (wf : WellFormedProgram p) (input : V2.Runtime.InputValid p env)
    (started : V2.Runtime.Start p env s) : V2.Runtime.Coherent p env s := by
  cases started with | boot hart dtb entered =>
    have typing := enter_typed wf entered wf.roles.boot (by simp [hart.type, dtb.type, wordTy]) rfl
    cases entered with | defined found =>
      refine ⟨typing.1, typing.2.1, typing.2.2, input.initialHardware, .inl rfl, .boot, .nil,
        .ordinary rfl, Nat.zero_le _, Nat.zero_lt_succ 0, ?_, ?_⟩
      · simp [V2.Runtime.startState]
      · simp [V2.Runtime.startState]

theorem hardware_reset_coherent (wf : WellFormedProgram p) (old : V2.Runtime.Coherent p env s)
    (reset : V2.Runtime.HardwareReset p s delivery next) : V2.Runtime.Coherent p env next := by
  have typing := hardware_reset_typed wf old.memory.1 reset
  cases reset with | handler cause pc auxiliary entered =>
    cases entered with | defined found =>
      refine ⟨typing.1, typing.2.1, typing.2.2, old.hardware, old.installed, .hardware, .nil,
        .ordinary rfl, old.cursor, old.ordinal, ?_, ?_⟩
      · simp [V2.Runtime.hardwareResetState]
      · intro snapshot eq
        simp only [V2.Runtime.hardwareResetState, Option.some.injEq] at eq
        subst snapshot
        exact old.snapshot

theorem language_reset_coherent (wf : WellFormedProgram p) (old : V2.Runtime.Coherent p env s)
    (reset : V2.Runtime.LanguageReset p s tag next) : V2.Runtime.Coherent p env next := by
  have typing := language_reset_typed wf old.memory.1 reset
  cases reset with | handler value entered =>
    cases entered with | defined found =>
      refine ⟨typing.1, typing.2.1, typing.2.2, old.hardware, old.installed, .language, .nil,
        .ordinary rfl, old.cursor, old.ordinal, ?_, ?_⟩
      · simp [V2.Runtime.languageResetState]
      · intro snapshot eq
        simp only [V2.Runtime.languageResetState, Option.some.injEq] at eq
        subst snapshot
        exact old.snapshot

private theorem invoke_legacy_return_typed (wf : WellFormedProgram p)
    (typed : Words.State.Typed p.carrier ⟨.invoke ident none values, a, k, w⟩ t)
    (found : p.functions[ident]? = some (.primitive row)) (operation : row.operation = .legacy op)
    (result : value.type = op.result) : Words.State.Typed p.carrier ⟨.ret value, a, k, w⟩ t := by
  have result' : value.type = row.result := by
    rw [(wf.at found).result, operation]
    exact result
  cases typed with | intro env control frames layout world =>
    cases control with | invoke signature _ _ _ =>
      have same := Option.some.inj (signature.symm.trans (V2.Runtime.primitive_carrier_signature found))
      cases same
      exact Words.typed_ret env (result' ▸ frames) layout world

private theorem returnLegacy_typed (wf : WellFormedProgram p)
    (typed : Words.State.Typed p.carrier s.machine t)
    (pending : V2.Runtime.LegacyPendingAt p s q) (result : value.type = q.operation.result) :
    Words.State.Typed p.carrier (V2.Runtime.returnLegacyState s value).machine t := by
  obtain ⟨values, row, controlEq, found, operation, _⟩ := pending.invocation
  cases s with | mk machine origins phase hardware episode stack cursor ordinal events used forwarding seen parked snapshot =>
    cases machine with | mk ctl a k w =>
      simp only at controlEq
      subst ctl
      exact invoke_legacy_return_typed wf typed found operation result

theorem legacy_return_coherent (wf : WellFormedProgram p) (old : V2.Runtime.Coherent p env s)
    (valid : V2.Runtime.LegacyAfterValid p s q value) :
    V2.Runtime.Coherent p env (V2.Runtime.returnLegacyState s value) :=
  ⟨returnLegacy_typed wf old.typed valid.1 valid.2.2, V2.Runtime.returnLegacy_aligned old.aligned valid.1,
    old.memory, old.hardware, old.installed, old.stack, old.episode, .ordinary rfl,
    old.cursor, old.ordinal, old.bootSeen, old.passive⟩

theorem forward_reset_coherent (wf : WellFormedProgram p) (old : V2.Runtime.Coherent p env s)
    (reset : V2.Runtime.ForwardReset p env s q next) : V2.Runtime.Coherent p env next := by
  have typing := forward_reset_typed wf old.memory.1 reset
  have hardware := reset.hardware_valid
  cases reset with | handler _ _ _ _ _ _ entered =>
    cases entered with | defined found =>
      refine ⟨typing.1, typing.2.1, typing.2.2, hardware, old.installed, .hardware, .nil,
        .ordinary rfl, old.cursor, old.ordinal, ?_, ?_⟩
      · simp [V2.Runtime.forwardResetState]
      · intro snapshot eq
        simp only [V2.Runtime.forwardResetState, Option.some.injEq] at eq
        subst snapshot
        exact old.snapshot

end ANL.Boot.V3.Runtime
