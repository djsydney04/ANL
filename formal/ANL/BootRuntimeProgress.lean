import ANL.BootRuntimeEffectCompletion

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program} {s : State}

/-- Only the defensive malformed-state outcome is excluded; both semantic blocks remain. -/
def GoodOutcome : TickResult → Prop
  | .invalidState _ => False
  | _ => True

 theorem ready_exists (safe : LocalSafety p env s) : ∃ cmd, Ready p s cmd := by
  cases safe.runtime.phase with
  | ordinary phase =>
    by_cases trapped : ∃ kind, s.machine.control = .trap kind
    · obtain ⟨kind, ctl⟩ := trapped
      obtain ⟨tag, tagged⟩ := safe.trap_tag ctl
      exact ⟨_, .language phase ctl tagged⟩
    · have nontrap : NonTrap s.machine.control := by
        cases ctl : s.machine.control <;> try trivial
        exact False.elim (trapped ⟨_, ctl⟩)
      by_cases first : FirstPark p s
      · exact ⟨_, .park phase first⟩
      · cases found : capture p s with
        | none => exact ⟨_, .ordinary phase nontrap first (capture_none_iff.mp found)⟩
        | some q => exact ⟨_, .capture phase first (capture_iff.mp found)⟩
  | before phase valid => exact ⟨_, .before phase valid⟩
  | commit phase valid => exact ⟨_, .commit phase valid⟩
  | after phase valid _ => exact ⟨_, .after phase valid⟩
  | finish phase valid _ => exact ⟨_, .finish phase valid⟩
  | parkWaiting phase valid => exact ⟨_, .parkCheck phase valid⟩
  | parkConsumed phase valid => exact ⟨_, .parkResume phase valid⟩

 theorem terminal_shape (terminal : Words.Terminal machine) :
    (∃ value, machine.control = .ret value ∧ machine.kont = []) ∨ (∃ kind, machine.control = .trap kind) := by
  cases terminal
  · exact .inl ⟨_, rfl, rfl⟩
  · exact .inr ⟨_, rfl⟩

 theorem ordinary_step_exists (wf : WellFormedProgram p) (safe : LocalSafety p env s)
    (ready : Ready p s .ordinary) : ∃ next origins, Origin.Step p noAllocations s.machine s.origins next origins := by
  have admitted := ordinary_admitted wf safe.runtime ready
  rcases Words.progress (responses := noAllocations) safe.runtime.typed with terminal | ⟨next, actual⟩
  · cases ready with | ordinary _ nontrap _ _ =>
     rcases terminal_shape terminal with ⟨value, eq⟩ | ⟨kind, eq⟩
     · exact False.elim (safe.not_empty_return value eq)
     · rw [eq] at nontrap
       exact False.elim nontrap
  · obtain ⟨origins, step⟩ := Origin.lift admitted safe.runtime.aligned actual
    exact ⟨next, origins, step⟩

 theorem Cut.progress (wf : WellFormedProgram p) (input : InputValid p env) :
    ∃ result, Cut p env s key fallback result ∧ GoodOutcome result := by
  cases present : deliveryAt env s key with
  | none => exact ⟨_, .absent (deliveryAt_none_iff.mp present), trivial⟩
  | some d =>
    have matched := deliveryAt_iff.mp present
    by_cases eligible : Eligible p s
    · obtain ⟨next, reset⟩ := delivery_reset_exists wf input matched
      exact ⟨_, .deliver matched eligible reset, trivial⟩
    · exact ⟨_, .ineligible matched eligible, trivial⟩

 theorem Ready.progress (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : LocalSafety p env s) (ready : Ready p s cmd) :
    ∃ result, Execute p env s cmd result ∧ GoodOutcome result := by
  cases ready with
  | language _ _ tag =>
    obtain ⟨next, reset⟩ := LanguageReset.exists (s := s) wf tag.bound
    exact ⟨_, .language reset, trivial⟩
  | park => exact ⟨_, .enterPark, trivial⟩
  | capture => exact ⟨_, .captured, trivial⟩
  | ordinary phase nontrap first absent =>
    obtain ⟨next, origins, step⟩ := ordinary_step_exists wf safe (.ordinary phase nontrap first absent)
    exact ⟨_, .ordinary step, trivial⟩
  | before =>
    obtain ⟨result, cut, good⟩ := Cut.progress (s := s) (key := .beforePrimitive _ _) (fallback := _) wf input
    exact ⟨result, .before cut, good⟩
  | commit _ valid =>
    rcases pending_effect_or_block input safe.runtime valid.1 with ⟨result, effect⟩ | blocked
    · exact ⟨_, .commit effect, trivial⟩
    · exact ⟨_, .blocked blocked, trivial⟩
  | after =>
    obtain ⟨result, cut, good⟩ := Cut.progress (s := s) (key := .afterPrimitive _ _) (fallback := _) wf input
    exact ⟨result, .after cut, good⟩
  | finish => exact ⟨_, .finish, trivial⟩
  | parkCheck =>
    by_cases boot : s.episode = .boot
    · obtain ⟨result, cut, good⟩ := Cut.progress (s := s) (key := .bootPark _) (fallback := _) wf input
      exact ⟨result, .parkBoot boot cut, good⟩
    · exact ⟨_, .parkHandler boot, trivial⟩
  | parkResume => exact ⟨_, .parkResume, trivial⟩

 theorem local_progress (wf : WellFormedProgram p) (input : InputValid p env) (safe : LocalSafety p env s) :
    GoodOutcome (tickRaw p env s) := by
  obtain ⟨cmd, ready⟩ := ready_exists safe
  obtain ⟨result, execution, good⟩ := ready.progress wf input safe
  have exactTick := (BootOutcome.ready ready execution).compute
  rw [exactTick]
  exact good

 theorem local_not_invalidState (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : LocalSafety p env s) : tickRaw p env s ≠ .invalidState bad := by
  intro eq
  have good := local_progress wf input safe
  rw [eq] at good
  exact good

end ANL.Boot.Runtime
