import ANL.WordsSafety

namespace ANL.Words

open ANL.Memory

theorem execute_preserves (wf : WellFormedProgram p) (h : State.Typed p s t) :
    State.Typed p (execute p responses budget s).state t := steps_preserve wf h execute_prefix

theorem execute_completed_safe (wf : WellFormedProgram p) (h : State.Typed p s t)
    (hr : execute p responses budget s = .completed last) : State.Typed p last t ∧ Terminal last := by
  obtain ⟨steps, stop⟩ := execute_completed_sound hr
  have typed := steps_preserve wf h steps
  refine ⟨typed, ?_⟩
  rcases stop with terminal | invalid
  · exact terminal
  · exact False.elim (typed.not_invalid invalid)

theorem execute_exhausted_safe (wf : WellFormedProgram p) (h : State.Typed p s t)
    (hr : execute p responses budget s = .exhausted last) :
    State.Typed p last t ∧ ∃ next, Step p responses last next := by
  obtain ⟨steps, stop⟩ := execute_exhausted_prefix hr
  have typed := steps_preserve wf h steps.steps
  refine ⟨typed, ?_⟩
  rcases progress (responses := responses) typed with terminal | next
  · have yes := rawStopped_iff.mpr (Or.inl terminal)
    rw [stop] at yes; contradiction
  · exact next

end ANL.Words
