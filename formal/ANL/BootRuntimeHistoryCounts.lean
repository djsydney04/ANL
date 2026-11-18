import ANL.BootRuntimeEventPrefixes

namespace ANL.Boot.Runtime
variable {hardware : Hardware}

/-- Current-summary projection. No event-list traversal or reverse is evaluated here. -/
def State.eventCount (s : State) : Nat :=
  s.nextOrdinal - 1 + if s.episode = .boot then 0 else 1

theorem event_length_partition (events : List Event) :
    events.length = (primitiveOrdinals events).length + resetCount events := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> simp_all [primitiveOrdinals, resetCount] <;> omega

theorem History.event_count (history : History p env events hardware cursor ordinal episode used) :
    events.length = ordinal - 1 + if episode = .boot then 0 else 1 := by
  have positive := history.ordinals.positive
  have length := history.ordinals.length
  rw [event_length_partition, history.reset_count]
  omega

theorem StateHistory.event_count (history : StateHistory p env s) :
    s.eventCount = s.revEvents.length := (History.event_count history).symm

theorem StateHistory.ordered_event_count (history : StateHistory p env s) :
    s.eventCount = s.events.length := by
  simp only [State.events, List.length_reverse, history.event_count]

theorem Start.event_count (started : Start p env s) : s.eventCount = 0 := by
  cases started
  rfl

/-- Exact endpoints and suffix for a finite prefix. History is required independently at both ends. -/
theorem BootStepsN.event_offsets (steps : BootStepsN p env n first last)
    (firstHistory : StateHistory p env first) (lastHistory : StateHistory p env last) :
    ∃ added, last.events = first.events ++ added ∧
      last.eventCount = first.eventCount + added.length ∧
      last.events.drop first.eventCount = added ∧ added.length ≤ n := by
  obtain ⟨added, traceEq, bound⟩ := steps.ordered_event_prefix
  refine ⟨added, traceEq, ?_, ?_, bound⟩
  · rw [firstHistory.ordered_event_count, lastHistory.ordered_event_count, traceEq, List.length_append]
  · rw [firstHistory.ordered_event_count, traceEq]
    simp

theorem BootStepsN.event_count_monotone (steps : BootStepsN p env n first last)
    (firstHistory : StateHistory p env first) (lastHistory : StateHistory p env last) :
    first.eventCount ≤ last.eventCount ∧ last.eventCount ≤ first.eventCount + n := by
  obtain ⟨_, _, count, _, bound⟩ := steps.event_offsets firstHistory lastHistory
  omega

theorem checked_prefix_event_count (wf : WellFormedProgram p) (input : InputValid p env)
    (started : Start p env first) (steps : BootStepsN p env n first last) :
    last.eventCount = last.events.length ∧ last.eventCount ≤ n := by
  have firstHistory := (started.safety wf input).history
  have lastHistory := (checked_entry_safety wf input started steps).history
  have bound := (steps.event_count_monotone firstHistory lastHistory).2
  rw [started.event_count, Nat.zero_add] at bound
  exact ⟨lastHistory.ordered_event_count, bound⟩

end ANL.Boot.Runtime
