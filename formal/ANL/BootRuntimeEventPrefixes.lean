import ANL.BootRuntimeAuthority

namespace ANL.Boot.Runtime
variable {p : ANL.Boot.Program} {s : State}

/-- An actual step retains the reverse trace or prepends exactly one transaction/reset event. -/
 theorem BootStep.event_change (step : BootStep p env s next) :
    next.revEvents = s.revEvents ∨ ∃ event, next.revEvents = event :: s.revEvents := by
  cases step with | advance _ execution =>
   cases execution with
   | language reset => cases reset; exact .inr ⟨_, rfl⟩
   | commit => exact .inr ⟨_, rfl⟩
   | before cut | after cut | parkBoot _ cut =>
     cases cut with
     | absent => exact .inl rfl
     | deliver _ _ reset => cases reset; exact .inr ⟨_, rfl⟩
   | enterPark | captured | ordinary | finish | parkHandler | parkResume => exact .inl rfl

 theorem BootStep.event_prefix (step : BootStep p env s next) :
    ∃ added, next.revEvents = added ++ s.revEvents ∧ added.length ≤ 1 := by
  rcases step.event_change with same | ⟨event, extended⟩
  · exact ⟨[], same, by decide⟩
  · exact ⟨[event], extended, by simp⟩

 theorem BootStepsN.event_prefix (steps : BootStepsN p env n s last) :
    ∃ added, last.revEvents = added ++ s.revEvents ∧ added.length ≤ n := by
  induction steps with
  | zero => exact ⟨[], rfl, by decide⟩
  | succ step _ ih =>
    obtain ⟨head, headEq, headBound⟩ := step.event_prefix
    obtain ⟨tail, tailEq, tailBound⟩ := ih
    refine ⟨tail ++ head, ?_, ?_⟩
    · rw [tailEq, headEq, List.append_assoc]
    · simp only [List.length_append]
      omega

 theorem BootStepsN.ordered_event_prefix (steps : BootStepsN p env n s last) :
    ∃ added, last.events = s.events ++ added ∧ added.length ≤ n := by
  obtain ⟨added, eq, bound⟩ := steps.event_prefix
  exact ⟨added.reverse, by simp [State.events, eq], by simpa using bound⟩

 theorem checked_prefix_events (wf : WellFormedProgram p) (input : InputValid p env) (started : Start p env first)
    (steps : BootStepsN p env n first last) :
    Consecutive last.nextOrdinal (primitiveOrdinals last.revEvents) ∧
    (readPayloads last.revEvents).reverse = env.reads.take last.readCursor ∧
    (readPayloads last.revEvents).length = last.readCursor ∧ resetCount last.revEvents ≤ 1 ∧
    last.revEvents.length ≤ n := by
  have safe := checked_entry_safety wf input started steps
  have history := safe.history
  refine ⟨history.ordinals, history.read_prefix, history.read_count, history.at_most_one_reset, ?_⟩
  obtain ⟨added, eq, bound⟩ := steps.event_prefix
  cases started
  rw [eq]
  simpa [startState] using bound

end ANL.Boot.Runtime
