import ANL.BootRuntimeSupported

namespace ANL.Boot.Runtime
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem resume_world : (resume result a k w).world = w := by cases result <;> rfl
 theorem arguments_world : (beginArguments f loan args values a k w).world = w := by cases args <;> rfl

 theorem admitted_world (admitted : Origin.Admitted p s) (step : Words.Step p.carrier responses s next) :
    next.world = s.world := by
  cases step <;> simp_all only [Origin.Admitted]
  all_goals first | rfl | exact resume_world | exact arguments_world

 theorem admitted_response_eq (admitted : Origin.Admitted p s) :
    Words.step p.carrier responses s = Words.step p.carrier other s := by
  cases s with | mk ctl a k w =>
   cases ctl <;> simp_all [Origin.Admitted, Words.step]

 theorem admitted_response_irrelevant (admitted : Origin.Admitted p s)
    (step : Words.Step p.carrier responses s next) : Words.Step p.carrier other s next := by
  apply Words.step_iff.mp
  rw [← admitted_response_eq (other := other) admitted]
  exact Words.step_complete step

 theorem OriginStep.response_irrelevant (step : Origin.Step p responses s origins next metadata) :
    Origin.Step p other s origins next metadata := by
  cases step with | ordinary admitted actual choice applied =>
    exact .ordinary admitted (admitted_response_irrelevant admitted actual) choice applied

 theorem empty_layout_resources (layout : Layout [] resources frames) : resources = [] := by
  cases resources with
  | nil => rfl
  | cons binding rest =>
    obtain ⟨shape, impossible, _⟩ := layout.live (List.mem_cons_self)
    cases impossible

 theorem aligned_frames_clean (aligned : Origin.StackAt p function origins frames) (layout : Layout [] resources frames) :
    ∀ frame ∈ frames, FrameClean frame := by
  induction aligned generalizing resources with
  | nil => simp
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    cases head
    all_goals first
      | exact ⟨trivial, ih (layout.pop_plain trivial)⟩
      | have facts := layout.call_inv
        exact ⟨⟨empty_layout_resources facts.2.2, rfl⟩, ih facts.2.2⟩

 theorem typed_aligned_memory (typed : Words.State.Typed p.carrier machine t)
    (aligned : Origin.Aligned p machine origins) (world : machine.world = .initial) : MemoryFreeState machine := by
  have layout := typed.layout
  rw [world] at layout
  exact ⟨world, empty_layout_resources layout, aligned_frames_clean aligned.frames layout⟩

/-- The caller-chain projection is independent of the current helper function. -/
def outerFunction (current : Nat) : List Frame → Nat
  | [] => current
  | .callReturn caller _ :: rest => outerFunction caller.function rest
  | _ :: rest => outerFunction current rest

 theorem outer_push (noCaller : ∀ caller loan, frame ≠ .callReturn caller loan) :
    outerFunction current (frame :: rest) = outerFunction current rest := by
  cases frame <;> first | rfl | exact False.elim (noCaller _ _ rfl)

 theorem EpisodeChain.outer_eq (chain : EpisodeChain current frames role) : outerFunction current frames = role := by
  induction chain with
  | nil => rfl
  | caller _ ih => exact ih
  | frame noCaller _ ih => exact (outer_push noCaller).trans ih

 theorem outer_eq_chain (same : outerFunction current frames = role) : EpisodeChain current frames role := by
  induction frames generalizing current with
  | nil => simpa [outerFunction] using same ▸ (EpisodeChain.nil (role := current))
  | cons frame rest ih =>
    cases frame
    all_goals first
      | exact .caller (ih same)
      | exact .frame (by intro caller loan impossible; cases impossible) (ih same)

 theorem resume_outer : outerFunction (resume result a k w).current.function (resume result a k w).kont = outerFunction a.function k := by
  cases result <;> rfl
 theorem arguments_outer : outerFunction (beginArguments f loan args values a k w).current.function
    (beginArguments f loan args values a k w).kont = outerFunction a.function k := by cases args <;> rfl

 theorem step_outer (step : Words.Step program responses s next) :
    outerFunction next.current.function next.kont = outerFunction s.current.function s.kont := by
  cases step
  all_goals first | rfl | exact resume_outer | exact arguments_outer

 theorem step_episode (chain : EpisodeChain s.current.function s.kont role)
    (step : Words.Step program responses s next) : EpisodeChain next.current.function next.kont role :=
  outer_eq_chain ((step_outer step).trans chain.outer_eq)

 theorem ordinary_local_preservation {s : State} (wf : WellFormedProgram p)
    (typed : Words.State.Typed p.carrier s.machine unitTy) (aligned : Origin.Aligned p s.machine s.origins)
    (memory : MemoryFreeState s.machine)
    (episode : EpisodeChain s.machine.current.function s.machine.kont (s.episode.function p))
    (step : Origin.Step p responses s.machine s.origins next origins) :
    Words.State.Typed p.carrier next unitTy ∧ Origin.Aligned p next origins ∧ MemoryFreeState next ∧
    EpisodeChain next.current.function next.kont (s.episode.function p) ∧ SupportedControl next.control := by
  have typing := Words.preservation (carrier_wellFormed wf) typed step.erase
  have alignment := Origin.preserve wf typed aligned step
  have world : next.world = .initial := by
    cases step with | ordinary admitted actual _ _ => exact (admitted_world admitted actual).trans memory.1
  exact ⟨typing, alignment, typed_aligned_memory typing alignment world,
    step_episode episode step.erase, OriginStep.supported step⟩

end ANL.Boot.Runtime
