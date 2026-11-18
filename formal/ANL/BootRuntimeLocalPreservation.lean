import ANL.BootRuntimeInterceptionSafety

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program} {s : State}
set_option linter.unusedSimpArgs false

 theorem ordinary_invariant (wf : WellFormedProgram p) (old : RuntimeInvariant p env s)
    (phase : s.phase = .ordinary) (step : Origin.Step p responses s.machine s.origins next origins) :
    RuntimeInvariant p env (ordinaryState s next origins) := by
  obtain ⟨typed, aligned, memory, episode, _⟩ :=
    ordinary_local_preservation wf old.typed old.aligned old.memory old.episode step
  exact ⟨typed, aligned, memory, old.hardware, old.installed, old.stack, episode,
    .ordinary phase, old.cursor, old.ordinal, old.bootSeen, old.passive⟩

 theorem before_invariant (old : RuntimeInvariant p env s) (valid : BeforeValid p s q) :
    RuntimeInvariant p env (withPhase s (.primitiveCommit q)) :=
  with_phase_invariant old (.commit rfl valid)

 theorem after_invariant (old : RuntimeInvariant p env s) (phase : s.phase = .primitiveAfter q v)
    (valid : AfterValid p s q v) : RuntimeInvariant p env (withPhase s (.primitiveReturn q v)) := by
  have latest : LatestCommit s q v := by
    cases old.phase <;> simp_all
  exact with_phase_invariant old (.finish rfl valid latest)

 theorem park_waiting_invariant (old : RuntimeInvariant p env s) (first : FirstPark p s) :
    RuntimeInvariant p env (withPhase s (.parkCheck s.origins.control)) :=
  with_phase_invariant old (.parkWaiting rfl first)

 theorem observed_park_invariant (old : RuntimeInvariant p env s) (waiting : ParkWaiting p s location) :
    RuntimeInvariant p env (observedPark s location) := by
  refine ⟨old.typed, old.aligned, old.memory, old.hardware, old.installed, old.stack, old.episode,
    .parkConsumed rfl ?_, old.cursor, old.ordinal, ?_, old.passive⟩
  · exact ⟨waiting.1, rfl, by intro boot; change s.episode = .boot at boot; simp [observedPark, boot]⟩
  · intro boot _
    simp only [observedPark] at boot ⊢
    simp [boot]

 theorem Cut.invariant (wf : WellFormedProgram p) (old : RuntimeInvariant p env s)
    (defaultValid : RuntimeInvariant p env fallback)
    (cut : Cut p env s key fallback (.advance next)) : RuntimeInvariant p env next := by
  cases cut with
  | absent => exact defaultValid
  | deliver _ _ reset => exact reset.invariant wf old

/-- Local preservation over the independent rules. No History or future-reachability hypothesis is used. -/
 theorem BootStep.invariant (wf : WellFormedProgram p) (old : RuntimeInvariant p env s)
    (step : BootStep p env s next) : RuntimeInvariant p env next := by
  cases step with | advance ready execution =>
   cases execution with
   | language reset => exact reset.invariant wf old
   | enterPark => cases ready with | park _ first => exact park_waiting_invariant old first
   | captured => cases ready with | capture _ _ captured => exact captured_invariant old captured
   | ordinary step => cases ready with | ordinary phase _ _ _ => exact ordinary_invariant wf old phase step
   | before cut => cases ready with | before _ valid => exact cut.invariant wf old (before_invariant old valid)
   | commit effect => cases ready with | commit _ valid => exact commit_invariant old valid effect
   | after cut => cases ready with | after phase valid => exact cut.invariant wf old (after_invariant old phase valid)
   | finish => cases ready with | finish _ valid => exact return_invariant wf old valid
   | parkBoot _ cut => cases ready with | parkCheck _ waiting => exact cut.invariant wf old (observed_park_invariant old waiting)
   | parkHandler => cases ready with | parkCheck _ waiting => exact observed_park_invariant old waiting
   | parkResume => exact with_phase_invariant old (.ordinary rfl)

 theorem HardwareReset.supported (reset : HardwareReset p s d next) : SupportedControl next.machine.control := by
  cases reset with | handler _ _ _ entered => cases entered; trivial
 theorem LanguageReset.supported (reset : LanguageReset p s tag next) : SupportedControl next.machine.control := by
  cases reset with | handler _ entered => cases entered; trivial
 theorem Start.supported (started : Start p env s) : SupportedControl s.machine.control := by
  cases started with | boot _ _ entered => cases entered; trivial

 theorem Cut.supported (defaultValid : SupportedControl fallback.machine.control)
    (cut : Cut p env s key fallback (.advance next)) : SupportedControl next.machine.control := by
  cases cut with
  | absent => exact defaultValid
  | deliver _ _ reset => exact reset.supported

 theorem BootStep.supported (old : SupportedControl s.machine.control)
    (step : BootStep p env s next) : SupportedControl next.machine.control := by
  cases step with | advance _ execution =>
   cases execution with
   | language reset => exact reset.supported
   | ordinary step => exact OriginStep.supported step
   | before cut | after cut | parkBoot _ cut =>
     cases cut with
     | absent => exact old
     | deliver _ _ reset => exact reset.supported
   | finish => trivial
   | enterPark | captured | commit | parkHandler | parkResume => exact old

/-- The executable API inherits the same local preservation; its result is not the invariant's definition. -/
 theorem tick_preserves (wf : WellFormedProgram p) (old : RuntimeInvariant p input.raw s)
    (advanced : tick p input s = .advance next) : RuntimeInvariant p input.raw next :=
  (tick_step_iff.mp advanced).invariant wf old

end ANL.Boot.Runtime
