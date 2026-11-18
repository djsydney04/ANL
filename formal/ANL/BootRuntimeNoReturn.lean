import ANL.BootRuntimeLocalPreservation
import ANL.BootNoReturn

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program} {s : State}

/-- Interception skips the carrier grant/body, but preserves the actual caller barrier. -/
 theorem shield_invoke_return (shield : ReturnShield depth ⟨.invoke ident none values, a, k, w⟩) :
    ReturnShield depth ⟨.ret value, a, k, w⟩ := by
  cases shield with | kont barrier => exact .kont barrier

 theorem return_shield (pending : PendingAt p s q) (shield : ReturnShield depth s.machine) :
    ReturnShield depth (returnState s value).machine := by
  obtain ⟨values, row, controlEq, _⟩ := pending.invocation
  cases s with | mk machine origins phase hardware episode stack cursor ordinal events used seen parked snapshot =>
   cases machine with | mk ctl a k w =>
    simp only at controlEq
    subst ctl
    exact shield_invoke_return shield

 theorem Start.shield (wf : WellFormedProgram p) (started : Start p env s) : ReturnShield 0 s.machine := by
  cases started with | boot _ _ entered =>
   cases entered with | defined found =>
    exact .eval (wf.roles.bootTail _ found) (Nat.zero_le _)

 theorem HardwareReset.shield (wf : WellFormedProgram p) (reset : HardwareReset p s d next) :
    ReturnShield 0 next.machine := by
  cases reset with | handler _ _ _ entered =>
   cases entered with | defined found =>
    apply ReturnShield.eval _ (Nat.zero_le _)
    rw [wf.roles.hardwareBody _ found]
    exact .letValue .park

 theorem LanguageReset.shield (wf : WellFormedProgram p) (reset : LanguageReset p s tag next) :
    ReturnShield 0 next.machine := by
  cases reset with | handler _ entered =>
   cases entered with | defined found =>
    apply ReturnShield.eval _ (Nat.zero_le _)
    rw [wf.roles.languageBody _ found]
    exact .letValue .park

/-- Administrative, effect, ordinary, interception, and reset steps all retain a real continuation shield. -/
 theorem BootStep.shield (wf : WellFormedProgram p) (old : ReturnShield 0 s.machine)
    (step : BootStep p env s next) : ReturnShield 0 next.machine := by
  cases step with | advance ready execution =>
   cases execution with
   | language reset => exact reset.shield wf
   | ordinary step => exact old.step step.erase
   | before cut | after cut | parkBoot _ cut =>
     cases cut with
     | absent => exact old
     | deliver _ _ reset => exact reset.shield wf
   | finish => cases ready with | finish _ valid => exact return_shield valid.1 old
   | enterPark | captured | commit | parkHandler | parkResume => exact old

 theorem shield_not_empty_return (shield : ReturnShield 0 s.machine) :
    ∀ value, ¬ (s.machine.control = .ret value ∧ s.machine.kont = []) := by
  intro value ⟨controlEq, empty⟩
  cases s with | mk machine origins phase hardware episode stack cursor ordinal events used seen parked snapshot =>
   cases machine with | mk ctl a k w =>
    simp only at controlEq empty
    subst ctl
    subst k
    exact Nat.not_lt_zero _ shield.return_depth

/-- A useful local package, independent of tick, reachability, History, and future outcomes. -/
structure LocalSafety (p : Program) (env : Environment) (s : State) : Prop where
  runtime : RuntimeInvariant p env s
  supported : SupportedControl s.machine.control
  shield : ReturnShield 0 s.machine

 theorem Start.localSafety (wf : WellFormedProgram p) (input : InputValid p env) (started : Start p env s) :
    LocalSafety p env s := ⟨started.invariant wf input, started.supported, started.shield wf⟩

 theorem BootStep.localSafety (wf : WellFormedProgram p) (old : LocalSafety p env s)
    (step : BootStep p env s next) : LocalSafety p env next :=
  ⟨step.invariant wf old.runtime, step.supported old.supported, step.shield wf old.shield⟩

 theorem LocalSafety.not_empty_return (safe : LocalSafety p env s) :
    ∀ value, ¬ (s.machine.control = .ret value ∧ s.machine.kont = []) := shield_not_empty_return safe.shield

 theorem LocalSafety.not_invalid (safe : LocalSafety p env s) : s.machine.control ≠ .invalid := by
  exact safe.runtime.typed.not_invalid

 theorem LocalSafety.trap_tag (safe : LocalSafety p env s) (trapped : s.machine.control = .trap kind) :
    ∃ tag, LanguageTag kind tag := by
  have supported := safe.supported
  rw [trapped] at supported
  exact supported

end ANL.Boot.Runtime
