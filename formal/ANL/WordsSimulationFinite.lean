import ANL.WordsExecute
import ANL.WordsMirRunProofs

namespace ANL.Words.Simulation

open ANL.Memory

inductive MirStepsN (p : Mir.Program) (responses : Responses) : Nat → Mir.State → Mir.State → Prop where
  | zero : MirStepsN p responses 0 s s
  | succ : Mir.Step p responses s middle → MirStepsN p responses n middle last →
      MirStepsN p responses (n + 1) s last

theorem MirStepsN.steps (h : MirStepsN p responses n s last) : Mir.Steps p responses s last := by
  induction h with
  | zero => exact .refl
  | succ hs _ ih => exact .cons hs ih

theorem MirStepsN.of_steps (h : Mir.Steps p responses s last) : ∃ n, MirStepsN p responses n s last := by
  induction h with
  | refl => exact ⟨0, .zero⟩
  | cons hs _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .succ hs hn⟩

theorem MirStepsN.prefix_remaining (segment : MirStepsN p responses m s middle)
    (whole : MirStepsN p responses n s last) (stop : Mir.RawStopped last) :
    m ≤ n ∧ MirStepsN p responses (n - m) middle last := by
  induction segment generalizing n with
  | zero => exact ⟨Nat.zero_le _, by simpa using whole⟩
  | succ hs _ ih =>
      cases whole with
      | zero => exact False.elim (stop.no_step hs)
      | succ ht rest =>
          have same := Mir.Step.deterministic hs ht
          subst same
          obtain ⟨hle, remaining⟩ := ih rest
          exact ⟨Nat.succ_le_succ hle, by simpa using remaining⟩

theorem mir_stopped_endpoints (left : Mir.Steps p responses s a)
    (right : Mir.Steps p responses s b) (ha : Mir.RawStopped a) (hb : Mir.RawStopped b) : a = b := by
  obtain ⟨m, hm⟩ := MirStepsN.of_steps left
  obtain ⟨n, hn⟩ := MirStepsN.of_steps right
  have remaining := (hm.prefix_remaining hn hb).2
  exact (ha.steps_eq remaining.steps).symm

private theorem finite_reflectionN
    (wf : WellFormedProgram p) (R : State → Mir.State → Prop) (rank : State → Nat)
    (F : State → Mir.State → Prop)
    (stepMatch : ∀ {s t next}, State.Typed p s ty → R s t → Step p responses s next →
      ∃ m t', MirStepsN q responses m t t' ∧ R next t' ∧ (m = 0 → rank next < rank s))
    (terminalFlush : ∀ {s t}, State.Typed p s ty → R s t → Terminal s →
      ∃ t', Mir.Steps q responses t t' ∧ Mir.Terminal t' ∧ F s t')
    (typed : State.Typed p s ty) (related : R s t)
    (path : MirStepsN q responses n t last) (stop : Mir.RawStopped last) :
    ∃ s', Steps p responses s s' ∧ Terminal s' ∧ F s' last := by
  generalize hsize : (n, rank s) = size
  induction size using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction generalizing n s t with
  | h size ih =>
      rcases progress (responses := responses) typed with terminal | ⟨next, hs⟩
      · obtain ⟨t', flush, done, observed⟩ := terminalFlush typed related terminal
        have same := mir_stopped_endpoints flush path.steps done.rawStopped stop
        exact ⟨s, .refl, terminal, same ▸ observed⟩
      · obtain ⟨m, t', segment, related', decreased⟩ := stepMatch typed related hs
        obtain ⟨hle, remaining⟩ := segment.prefix_remaining path stop
        have smaller : Prod.Lex Nat.lt Nat.lt (n - m, rank next) size := by
          rw [← hsize]
          by_cases zero : m = 0
          · simpa only [zero, Nat.sub_zero] using
              (Prod.Lex.right (ra := Nat.lt) (rb := Nat.lt) n (decreased zero))
          · exact Prod.Lex.left _ _ (by change n - m < n; omega)
        obtain ⟨s', source, terminal, observed⟩ := ih (n - m, rank next) smaller
          (preservation wf typed hs) related' remaining rfl
        exact ⟨s', .head hs source, terminal, observed⟩

theorem finite_reflection
    (wf : WellFormedProgram p) (R : State → Mir.State → Prop) (rank : State → Nat)
    (F : State → Mir.State → Prop)
    (stepMatch : ∀ {s t next}, State.Typed p s ty → R s t → Step p responses s next →
      ∃ m t', MirStepsN q responses m t t' ∧ R next t' ∧ (m = 0 → rank next < rank s))
    (terminalFlush : ∀ {s t}, State.Typed p s ty → R s t → Terminal s →
      ∃ t', Mir.Steps q responses t t' ∧ Mir.Terminal t' ∧ F s t')
    (typed : State.Typed p s ty) (related : R s t)
    (path : Mir.Steps q responses t last) (stop : Mir.RawStopped last) :
    ∃ s', Steps p responses s s' ∧ Terminal s' ∧ F s' last := by
  obtain ⟨n, pathN⟩ := MirStepsN.of_steps path
  exact finite_reflectionN wf R rank F stepMatch terminalFlush typed related pathN stop

theorem finite_forward
    (wf : WellFormedProgram p) (R : State → Mir.State → Prop) (F : State → Mir.State → Prop)
    (stepMatch : ∀ {s t next}, State.Typed p s ty → R s t → Step p responses s next →
      ∃ m t', MirStepsN q responses m t t' ∧ R next t')
    (terminalFlush : ∀ {s t}, State.Typed p s ty → R s t → Terminal s →
      ∃ t', Mir.Steps q responses t t' ∧ Mir.Terminal t' ∧ F s t')
    (typed : State.Typed p s ty) (related : R s t)
    (path : Steps p responses s last) (stop : Terminal last) :
    ∃ t', Mir.Steps q responses t t' ∧ Mir.Terminal t' ∧ F last t' := by
  induction path generalizing t with
  | refl => exact terminalFlush typed related stop
  | head hs _ ih =>
      obtain ⟨m, t', segment, related'⟩ := stepMatch typed related hs
      obtain ⟨last', remaining, terminal, observed⟩ := ih (preservation wf typed hs) related' stop
      exact ⟨last', segment.steps.trans remaining, terminal, observed⟩

end ANL.Words.Simulation
