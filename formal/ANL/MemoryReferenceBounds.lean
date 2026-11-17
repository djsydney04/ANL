import ANL.MemoryReference

namespace ANL.Memory.Reference

 theorem run_steps_bound : ∃ n, n ≤ budget ∧ StepsN p responses n c.machine
    (Tool.run p responses budget c).configuration.machine := by
  induction budget generalizing c with
  | zero => unfold Tool.run; split <;> exact ⟨0, Nat.le_refl _, .zero⟩
  | succ budget ih =>
    unfold Tool.run
    cases ht : Tool.tick p responses c with
    | completed last =>
      refine ⟨0, Nat.zero_le _, ?_⟩
      change StepsN p responses 0 c.machine last.machine
      rw [(Tool.tick_completed ht).1]
      exact .zero
    | resourceLimit reason last =>
      refine ⟨0, Nat.zero_le _, ?_⟩
      change StepsN p responses 0 c.machine last.machine
      rw [(Tool.tick_resource ht).1]
      exact .zero
    | advanced next =>
      obtain ⟨n, bound, path⟩ := ih (c := next)
      exact ⟨n + 1, by omega, .succ (Tool.tick_advanced ht) path⟩

def TraceGrowth (before after : World) : Prop :=
  ∃ events, events.length ≤ 1 ∧ after.trace = before.trace ++ events

 theorem trace_refl : TraceGrowth w w := ⟨[], by decide, by simp⟩

 theorem allocation_trace_growth : TraceGrowth w (allocate p responses w site n init).2 := by
  unfold allocate
  split
  · exact trace_refl
  · split
    · exact ⟨[.emptyOpen w.nextEmpty site], by simp, by simp [World.trace]⟩
    · cases responses w.nextRequest with
      | success => exact ⟨[.request w.nextRequest site n .success], by simp, by simp [World.trace]⟩
      | refused => exact ⟨[.request w.nextRequest site n .refused], by simp, by simp [World.trace]⟩

 theorem allocation_result_trace_growth (h : allocate p responses w site n init = (tag, next)) :
    TraceGrowth w next := by
  have hg := allocation_trace_growth (p := p) (responses := responses) (w := w) (site := site) (n := n) (init := init)
  simpa only [h] using hg

 theorem write_trace_growth (h : w.write r i value = some next) : TraceGrowth w next := by
  unfold World.write at h
  cases hw : Store.write w.owners r i value <;> simp only [hw, Option.map] at h
  · cases h
  · cases h; exact trace_refl

 theorem close_trace_growth (h : w.close r site = some next) : TraceGrowth w next :=
  ⟨[r.closeEvent site], by simp, World.close_trace h⟩

 theorem resume_world : (resume result a k w).world = w := by cases result <;> rfl
 theorem arguments_world : (beginArguments f loan args values a k w).world = w := by cases args <;> rfl

 theorem step_trace_growth (hs : Step p responses s next) : TraceGrowth s.world next.world := by
  cases hs
  all_goals try exact trace_refl
  all_goals try { simp only [resume_world, arguments_world]; exact trace_refl }
  case allocated => exact allocation_result_trace_growth ‹_›
  case allocationRefused => exact allocation_result_trace_growth ‹_›
  case allocationRejected => exact allocation_result_trace_growth ‹_›
  case stored => exact write_trace_growth ‹_›
  case closed => exact close_trace_growth ‹_›

 theorem steps_trace_growth (hs : StepsN p responses n s next) :
    ∃ events, events.length ≤ n ∧ next.world.trace = s.world.trace ++ events := by
  induction hs with
  | zero => exact ⟨[], by decide, by simp⟩
  | succ first rest ih =>
    obtain ⟨one, bound, hone⟩ := step_trace_growth first
    obtain ⟨tail, tailBound, htail⟩ := ih
    refine ⟨one ++ tail, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · rw [htail, hone, List.append_assoc]

 theorem run_trace_bound : ∃ events, events.length ≤ budget ∧
    (Tool.run p responses budget c).configuration.machine.world.trace = c.machine.world.trace ++ events := by
  obtain ⟨n, hn, path⟩ := run_steps_bound (p := p) (responses := responses) (budget := budget) (c := c)
  obtain ⟨events, bound, he⟩ := steps_trace_growth path
  exact ⟨events, by omega, he⟩

 theorem run_entry_event_bound :
    (Tool.run p responses budget (Tool.initial p fuel)).configuration.machine.world.revTrace.length ≤ budget := by
  obtain ⟨events, bound, he⟩ := run_trace_bound (p := p) (responses := responses)
    (budget := budget) (c := Tool.initial p fuel)
  simp only [Tool.initial, initial, World.initial, World.trace, List.reverse_nil, List.nil_append] at he
  have size := congrArg List.length he
  simp only [List.length_reverse] at size
  rw [← size] at bound
  simpa only [Tool.initial, initial, World.initial] using bound

end ANL.Memory.Reference
