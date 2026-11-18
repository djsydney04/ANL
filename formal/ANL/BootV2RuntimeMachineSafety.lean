import ANL.BootV2RuntimeCoherence
import ANL.BootRuntimeOrdinarySafety

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (FrameClean MemoryFreeState empty_layout_resources)
variable {p : ANL.Boot.V2.Program} {env : Environment} {s : State}
set_option linter.unusedSimpArgs false

theorem admitted_world (admitted : Origin.Admitted p machine)
    (step : Words.Step p.carrier responses machine nextMachine) : nextMachine.world = machine.world := by
  cases step <;> simp_all only [Origin.Admitted]
  all_goals first | rfl | exact ANL.Boot.Runtime.resume_world | exact ANL.Boot.Runtime.arguments_world

theorem aligned_frames_clean (aligned : Origin.StackAt p function origins frames)
    (layout : Layout [] resources frames) : ∀ frame ∈ frames, FrameClean frame := by
  induction aligned generalizing resources with
  | nil => simp
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    cases head
    all_goals first
      | exact ⟨trivial, ih (layout.pop_plain trivial)⟩
      | have facts := layout.call_inv
        exact ⟨⟨empty_layout_resources facts.2.2, rfl⟩, ih facts.2.2⟩

theorem typed_aligned_memory (typed : Words.State.Typed p.carrier machine resultTy)
    (aligned : Origin.Aligned p machine origins) (world : machine.world = .initial) : MemoryFreeState machine := by
  have layout := typed.layout
  rw [world] at layout
  exact ⟨world, empty_layout_resources layout, aligned_frames_clean aligned.frames layout⟩

theorem ordinary_local_coherent (wf : WellFormedProgram p) (old : Coherent p env s)
    (phase : s.phase = .legacy .ordinary)
    (step : Origin.Step p responses s.machine s.origins machine origins) :
    Coherent p env (ordinaryState s machine origins) := by
  have typing := Words.preservation (carrier_wellFormed wf) old.typed step.erase
  have alignment := Origin.preserve wf old.typed old.aligned step
  have world : machine.world = .initial := by
    cases step with | ordinary admitted actual _ _ => exact (admitted_world admitted actual).trans old.memory.1
  exact ⟨typing, alignment, typed_aligned_memory typing alignment world, old.hardware, old.installed,
    old.stack, ANL.Boot.Runtime.step_episode old.episode step.erase, .ordinary phase,
    old.cursor, old.ordinal, old.bootSeen, old.passive⟩

theorem Start.coherent (wf : WellFormedProgram p) (input : InputValid p env) (started : Start p env s) :
    Coherent p env s := by
  have typing := started.typed wf
  cases started with | boot hart dtb entered =>
   cases entered with | defined found =>
    refine ⟨typing.1, typing.2, ?_, input.initialHardware, .inl rfl, .boot, .nil,
      .ordinary rfl, Nat.zero_le _, Nat.zero_lt_succ 0, ?_, ?_⟩
    · exact ⟨rfl, rfl, by simp [startState]⟩
    · simp [startState]
    · simp [startState]

theorem HardwareReset.coherent (wf : WellFormedProgram p) (old : Coherent p env s)
    (reset : HardwareReset p s delivery next) : Coherent p env next := by
  have typing := reset.typed wf old.memory.1
  cases reset with | handler cause pc auxiliary entered =>
   cases entered with | defined found =>
    refine ⟨typing.1, typing.2, ?_, old.hardware, old.installed, .hardware, .nil,
      .ordinary rfl, old.cursor, old.ordinal, ?_, ?_⟩
    · exact ⟨old.memory.1, rfl, by simp [hardwareResetState]⟩
    · simp [hardwareResetState]
    · intro snapshot eq
      simp only [hardwareResetState, Option.some.injEq] at eq
      subst snapshot
      exact old.snapshot

theorem LanguageReset.coherent (wf : WellFormedProgram p) (old : Coherent p env s)
    (reset : LanguageReset p s tag next) : Coherent p env next := by
  have typing := reset.typed wf old.memory.1
  cases reset with | handler value entered =>
   cases entered with | defined found =>
    refine ⟨typing.1, typing.2, ?_, old.hardware, old.installed, .language, .nil,
      .ordinary rfl, old.cursor, old.ordinal, ?_, ?_⟩
    · exact ⟨old.memory.1, rfl, by simp [languageResetState]⟩
    · simp [languageResetState]
    · intro snapshot eq
      simp only [languageResetState, Option.some.injEq] at eq
      subst snapshot
      exact old.snapshot

end ANL.Boot.V2.Runtime
