import ANL.MemorySafety

namespace ANL.Memory

def isStopped (s : State) : Bool :=
  match s.control with
  | .ret _ => s.kont.isEmpty
  | .trap _ | .invalid => true
  | _ => false

def RawStopped (s : State) : Prop := Terminal s ∨ s.control = .invalid

theorem isStopped_iff : isStopped s = true ↔ step p responses s = none := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp [isStopped, step]
  case ret value => cases k <;> simp

theorem rawStopped_iff : isStopped s = true ↔ RawStopped s := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp [isStopped, RawStopped, terminal_iff]

inductive RunResult where
  | completed (state : State)
  | exhausted (state : State)
  deriving Repr

def RunResult.state : RunResult → State
  | .completed state | .exhausted state => state

/-- Retains the exact cutoff state. Budget zero never evaluates a semantic transition. -/
def execute (p : Program) (responses : Responses) : Nat → State → RunResult
  | 0, s => if isStopped s then .completed s else .exhausted s
  | budget + 1, s => match step p responses s with
    | none => .completed s
    | some next => execute p responses budget next

inductive StepsN (p : Program) (responses : Responses) : Nat → State → State → Prop where
  | zero : StepsN p responses 0 s s
  | succ : Step p responses s middle → StepsN p responses n middle last → StepsN p responses (n + 1) s last

theorem StepsN.steps (h : StepsN p responses n s last) : Steps p responses s last := by
  induction h with | zero => exact .refl | succ hs _ ih => exact .head hs ih

theorem execute_prefix : Steps p responses s (execute p responses budget s).state := by
  induction budget generalizing s with
  | zero => unfold execute; split <;> exact .refl
  | succ budget ih =>
    unfold execute
    cases hs : step p responses s with
    | none => exact .refl
    | some next => exact .head (step_sound hs) (ih (s := next))

theorem execute_completed_sound (h : execute p responses budget s = .completed last) :
    Steps p responses s last ∧ RawStopped last := by
  refine ⟨by simpa [h, RunResult.state] using (execute_prefix (p := p) (responses := responses) (budget := budget) (s := s)), ?_⟩
  induction budget generalizing s with
  | zero =>
    unfold execute at h
    split at h
    next stop => cases h; exact rawStopped_iff.mp stop
    next _ => cases h
  | succ budget ih =>
    unfold execute at h
    cases hs : step p responses s with
    | none => rw [hs] at h; cases h; exact stopped_iff.mp hs
    | some next => rw [hs] at h; exact ih h

theorem execute_completed_complete (h : Steps p responses s last) (stop : RawStopped last) :
    ∃ budget, execute p responses budget s = .completed last := by
  induction h with
  | refl => exact ⟨0, by simp [execute, rawStopped_iff.mpr stop]⟩
  | head hs _ ih =>
    obtain ⟨budget, hr⟩ := ih stop
    exact ⟨budget + 1, by simp [execute, step_complete hs, hr]⟩

theorem execute_completed_iff :
    (∃ budget, execute p responses budget s = .completed last) ↔ Steps p responses s last ∧ RawStopped last := by
  constructor
  · rintro ⟨budget, h⟩; exact execute_completed_sound h
  · rintro ⟨h, stop⟩; exact execute_completed_complete h stop

theorem execute_exhausted_prefix (h : execute p responses budget s = .exhausted last) :
    StepsN p responses budget s last ∧ isStopped last = false := by
  induction budget generalizing s with
  | zero =>
    unfold execute at h
    split at h
    next _ => cases h
    next stop => cases h; exact ⟨.zero, Bool.eq_false_iff.mpr stop⟩
  | succ budget ih =>
    unfold execute at h
    cases hs : step p responses s with
    | none => rw [hs] at h; cases h
    | some next =>
      rw [hs] at h
      obtain ⟨steps, stop⟩ := ih h
      exact ⟨.succ (step_sound hs) steps, stop⟩

theorem execute_exhausted_complete (h : StepsN p responses budget s last) (stop : isStopped last = false) :
    execute p responses budget s = .exhausted last := by
  induction h with
  | zero => simp [execute, stop]
  | succ hs _ ih => simp [execute, step_complete hs, ih stop]

theorem execute_exhausted_iff : execute p responses budget s = .exhausted last ↔
    StepsN p responses budget s last ∧ isStopped last = false :=
  ⟨execute_exhausted_prefix, fun ⟨steps, stop⟩ => execute_exhausted_complete steps stop⟩

theorem execute_zero : execute p responses 0 s =
    if isStopped s then .completed s else .exhausted s := rfl

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

end ANL.Memory
