import ANL.BootRuntimeInvariant
import ANL.BootRuntimeTickProofs

namespace ANL.Boot.Runtime
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem Start.exists (wf : WellFormedProgram p) (input : InputValid p env) : ∃ s, Start p env s := by
  cases wf.roles.boot with
  | intro found _ _ _ =>
    exact ⟨_, .boot (.value input.hart) (.value input.opaqueDtb) (.defined found)⟩

 theorem HardwareReset.exists (wf : WellFormedProgram p) (valid : DeliveryValid p d) :
    ∃ next, HardwareReset p s d next := by
  cases wf.roles.hardware with
  | intro found _ _ _ =>
    exact ⟨_, .handler (.value valid.cause) (.value valid.pc) (.value valid.auxiliary) (.defined found)⟩

 theorem LanguageReset.exists (wf : WellFormedProgram p) (bound : tag < byteModulus) :
    ∃ next, LanguageReset p s tag next := by
  cases wf.roles.language with
  | intro found _ _ _ => exact ⟨_, .handler (.value bound) (.defined found)⟩

 theorem LanguageTag.bound (tagged : LanguageTag trap tag) : tag < byteModulus := by cases tagged <;> decide

 theorem validated_start_exists (wf : WellFormedProgram p) (input : ValidatedInput p) : ∃ s, start p input = some s := by
  obtain ⟨s, hs⟩ := Start.exists wf input.valid
  exact ⟨s, startRaw_iff.mpr hs⟩

 theorem delivery_reset_exists (wf : WellFormedProgram p) (input : InputValid p env)
    (present : DeliveryAt env s key d) : ∃ next, HardwareReset p s d next :=
  HardwareReset.exists wf (present.valid input)

 theorem RuntimeInvariant.snapshot (invariant : RuntimeInvariant p env s) : SnapshotInvariant p s.snapshot :=
  ⟨invariant.typed, invariant.aligned, invariant.memory, invariant.stack, invariant.episode⟩

 theorem Start.invariant (wf : WellFormedProgram p) (input : InputValid p env) (started : Start p env s) :
    RuntimeInvariant p env s := by
  have typing := started.typed wf
  cases started with | boot hart dtb entered =>
   cases entered with | defined found =>
    refine ⟨typing.1, typing.2, ?_, input.initialHardware, .inl rfl, .boot, .nil,
      .ordinary rfl, Nat.zero_le _, Nat.zero_lt_succ 0, ?_, ?_⟩
    · exact ⟨rfl, rfl, by simp [startState]⟩
    · simp [startState]
    · simp [startState]

 theorem HardwareReset.invariant (wf : WellFormedProgram p) (old : RuntimeInvariant p env s)
    (reset : HardwareReset p s d next) : RuntimeInvariant p env next := by
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

 theorem LanguageReset.invariant (wf : WellFormedProgram p) (old : RuntimeInvariant p env s)
    (reset : LanguageReset p s tag next) : RuntimeInvariant p env next := by
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

/-- The static input gateway supplies reset words/role availability; a cut can still be dynamically ineligible. -/
 theorem eligible_cut_advances (wf : WellFormedProgram p) (input : InputValid p env)
    (present : DeliveryAt env s key d) (eligible : Eligible p s) :
    ∃ next, atCut p env s key fallback = .advance next ∧ HardwareReset p s d next := by
  obtain ⟨next, reset⟩ := delivery_reset_exists wf input present
  exact ⟨next, (Cut.deliver present eligible reset).compute, reset⟩

end ANL.Boot.Runtime
