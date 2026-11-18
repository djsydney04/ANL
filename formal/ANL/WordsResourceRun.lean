import ANL.WordsResources

namespace ANL.Words.Tool

open ANL.Memory

 theorem commit_projection : (commit p responses s m).map Configuration.machine = step p responses s := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp only [commit]
  all_goals try { cases step p responses _ <;> rfl }
  case allocate site n init yes no =>
    cases ha : allocate p.profile responses w site n init with
    | mk result next => cases result <;> simp [step, ha]

 theorem commit_sound (h : commit p responses s m = some next) :
    Step p responses s next.machine := by
  have hp := commit_projection (p := p) (responses := responses) (s := s) (m := m)
  rw [h] at hp
  exact step_sound hp.symm

 theorem commit_none (h : commit p responses s m = none) : isStopped s = true := by
  have hp := commit_projection (p := p) (responses := responses) (s := s) (m := m)
  rw [h] at hp
  exact isStopped_iff.mpr hp.symm

 theorem tick_advanced (h : tick p responses c = .advanced next) :
    Step p responses c.machine next.machine := by
  unfold tick at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      next hc => cases h; exact commit_sound hc

 theorem tick_completed (h : tick p responses c = .completed last) :
    last.machine = c.machine ∧ isStopped last.machine = true := by
  unfold tick at h
  split at h
  next stopped => cases h; exact ⟨rfl, stopped⟩
  next notStopped =>
    split at h
    · cases h
    · split at h
      next hc => exact False.elim (notStopped (commit_none hc))
      · cases h

 theorem tick_resource (h : tick p responses c = .resourceLimit reason last) :
    last.machine = c.machine ∧ preflight p c.machine c.meter = .blocked reason last.meter ∧
      isStopped c.machine = false := by
  unfold tick at h
  split at h
  · cases h
  next notStopped =>
    split at h
    next hp => cases h; exact ⟨rfl, hp, Bool.eq_false_iff.mpr notStopped⟩
    · split at h <;> cases h

 theorem run_zero : run p responses 0 c =
    if isStopped c.machine then .completed c else .exhausted c := rfl

 theorem run_prefix : Steps p responses c.machine (run p responses budget c).configuration.machine := by
  induction budget generalizing c with
  | zero => unfold run; split <;> exact .refl
  | succ budget ih =>
    unfold run
    cases ht : tick p responses c with
    | completed last => change Steps p responses c.machine last.machine; rw [(tick_completed ht).1]; exact .refl
    | resourceLimit reason last => change Steps p responses c.machine last.machine; rw [(tick_resource ht).1]; exact .refl
    | advanced next => exact .head (tick_advanced ht) (ih (c := next))

 theorem run_completed (h : run p responses budget c = .completed last) :
    Steps p responses c.machine last.machine ∧ RawStopped last.machine := by
  refine ⟨by simpa [h, Result.configuration] using (run_prefix (p := p) (responses := responses) (budget := budget) (c := c)), ?_⟩
  induction budget generalizing c with
  | zero =>
    unfold run at h; split at h
    next stop => cases h; exact rawStopped_iff.mp stop
    · cases h
  | succ budget ih =>
    unfold run at h
    cases ht : tick p responses c with
    | completed done => rw [ht] at h; cases h; exact rawStopped_iff.mp (tick_completed ht).2
    | resourceLimit reason done => rw [ht] at h; cases h
    | advanced next => rw [ht] at h; exact ih h

 theorem run_exhausted (h : run p responses budget c = .exhausted last) :
    StepsN p responses budget c.machine last.machine ∧ isStopped last.machine = false := by
  induction budget generalizing c with
  | zero =>
    unfold run at h; split at h
    · cases h
    next stop => cases h; exact ⟨.zero, Bool.eq_false_iff.mpr stop⟩
  | succ budget ih =>
    unfold run at h
    cases ht : tick p responses c with
    | completed done => rw [ht] at h; cases h
    | resourceLimit reason done => rw [ht] at h; cases h
    | advanced next =>
      rw [ht] at h
      obtain ⟨steps, stop⟩ := ih h
      exact ⟨.succ (tick_advanced ht) steps, stop⟩

 theorem run_resource (h : run p responses budget c = .resourceLimit reason last) :
    Steps p responses c.machine last.machine ∧ isStopped last.machine = false := by
  refine ⟨by simpa [h, Result.configuration] using (run_prefix (p := p) (responses := responses) (budget := budget) (c := c)), ?_⟩
  induction budget generalizing c with
  | zero => unfold run at h; split at h <;> cases h
  | succ budget ih =>
    unfold run at h
    cases ht : tick p responses c with
    | completed done => rw [ht] at h; cases h
    | resourceLimit why done =>
      rw [ht] at h; cases h
      obtain ⟨same, _, stop⟩ := tick_resource ht
      simpa [same] using stop
    | advanced next => rw [ht] at h; exact ih h

 theorem run_preserves (wf : WellFormedProgram p) (typed : State.Typed p c.machine ty) :
    State.Typed p (run p responses budget c).configuration.machine ty :=
  steps_preserve wf typed run_prefix

 theorem run_completed_safe (wf : WellFormedProgram p) (typed : State.Typed p c.machine ty)
    (hr : run p responses budget c = .completed last) : State.Typed p last.machine ty ∧ Terminal last.machine := by
  obtain ⟨steps, stop⟩ := run_completed hr
  have safe := steps_preserve wf typed steps
  refine ⟨safe, ?_⟩
  rcases stop with terminal | invalid
  · exact terminal
  · exact False.elim (safe.not_invalid invalid)

 theorem run_entry_safe (wf : WellFormedProgram p) :
    State.Typed p (run p responses budget (initial p fuel)).configuration.machine (.scalar (.legacy .i64)) :=
  run_preserves wf (entry_typed wf)

 theorem run_entry_no_invalid (wf : WellFormedProgram p) :
    (run p responses budget (initial p fuel)).configuration.machine.control ≠ .invalid :=
  (run_entry_safe wf).not_invalid

 theorem unwind_machine : (unwind c).machine = c.machine := rfl
 theorem unwind_trace : (unwind c).machine.world.trace = c.machine.world.trace := rfl
 theorem unwind_reservations : (unwind c).meter.slots = 0 ∧ (unwind c).meter.liveCells = 0 := ⟨rfl, rfl⟩

end ANL.Words.Tool
