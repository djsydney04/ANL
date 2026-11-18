import ANL.BootOriginAlignment

namespace ANL.Boot.Origin
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem action_exists (allowed : Admitted p s) (actual : ANL.Words.Step p.carrier responses s next) :
    ∃ a, action s next = some a := by
  cases actual <;> simp_all [Admitted, action]
  case call => rename_i ty f args a k w; cases args <;> simp
  case argumentReturn => rename_i v a f loan rest values k w; cases rest <;> simp
  all_goals repeat' split <;> simp_all

 theorem applies_exists {next : State} (choice : Chooses s.control s.kont next.control a) (allowed : Admitted p s)
    (lengths : m.frames.length = s.kont.length) : ∃ n, Applies a m n := by
  cases m with | mk ctl frames =>
   cases a with
   | keep => exact ⟨_, .keep⟩
   | push e => exact ⟨_, .push⟩
   | enter f => exact ⟨_, .enter⟩
   | pop | within | select =>
     cases frames with
     | cons parent rest => exact ⟨_, by constructor⟩
     | nil =>
       have empty : s.kont = [] := List.length_eq_zero_iff.mp lengths.symm
       cases s with | mk control current kont world =>
        simp only at empty
        subst kont
        cases choice <;> simp_all [Admitted]

 theorem lift (allowed : Admitted p s) (aligned : Aligned p s m)
    (actual : ANL.Words.Step p.carrier responses s next) : ∃ n, Step p responses s m next n := by
  obtain ⟨a, ha⟩ := action_exists allowed actual
  have choice := action_sound ha
  obtain ⟨n, hn⟩ := applies_exists choice allowed aligned.frames.length
  exact ⟨n, .ordinary allowed actual choice hn⟩

 theorem primitive_step_none (frontier : PrimitiveFrontier p s) : step p responses s m = none := by
  simp [step, checkAdmitted, primitive_not_admitted frontier]

 theorem step_none_iff (aligned : Aligned p s m) : step p responses s m = none ↔
    ¬ Admitted p s ∨ ANL.Words.step p.carrier responses s = none := by
  constructor
  · intro stopped
    by_cases allowed : Admitted p s
    · right
      cases h : ANL.Words.step p.carrier responses s with
      | none => rfl
      | some next =>
        obtain ⟨n, hn⟩ := lift allowed aligned (ANL.Words.step_sound h)
        rw [step_iff.mpr hn] at stopped
        cases stopped
    · exact Or.inl allowed
  · rintro (denied | stopped)
    · simp [step, checkAdmitted, denied]
    · simp [step, stopped]

 theorem FrameAt.return_admitted (h : FrameAt p f o frame outer) :
    Admitted p ⟨.ret v, current, frame :: k, w⟩ := by cases h <;> trivial

 theorem StackAt.call_no_loan (h : StackAt p f origins (.callReturn caller loan :: k)) : loan = none := by
  cases h with | cons head _ => cases head; rfl

 theorem frontier_or_admitted (wf : WellFormedProgram p) (typed : State.Typed p.carrier s t)
    (aligned : Aligned p s m) : PrimitiveFrontier p s ∨ Admitted p s := by
  cases m with | mk origin origins =>
   cases s with | mk ctl current kont world =>
    obtain ⟨hf, hc, hk⟩ := aligned
    simp only at hf hc hk
    cases hc with
    | eval located =>
      have free := located.memoryFree wf
      rename_i e
      cases e <;> simp_all [MemoryFree, Admitted]
    | ret located =>
      right
      cases kont with
      | nil => trivial
      | cons frame rest =>
        cases hk with | cons head _ => exact head.return_admitted
    | invoke located arity =>
      have target := located.call_target wf
      rename_i ty f args values
      cases found : p.functions[f]? with
      | none =>
        have bound := List.getElem?_eq_none_iff.mp found
        omega
      | some row =>
        cases row with
        | defined d => exact Or.inr ⟨target.2, by simp [found]⟩
        | primitive op => exact Or.inl ⟨f, values, op, rfl, found⟩
    | grant _ _ target => exact Or.inr target
    | revoke located =>
      right
      cases typed with | intro env control frames layout world =>
       cases control with | revoke shape =>
        simp only at shape
        subst kont
        have noLoan := hk.call_no_loan
        subst noLoan
        trivial
    | restore located =>
      right
      cases typed with | intro env control frames layout world =>
       cases control with | restore shape =>
        simp only at shape
        subst kont
        have noLoan := hk.call_no_loan
        subst noLoan
        trivial
    | trap | invalid => exact Or.inr trivial

 theorem stopped_iff (wf : WellFormedProgram p) (typed : State.Typed p.carrier s t)
    (aligned : Aligned p s m) : step p responses s m = none ↔
    PrimitiveFrontier p s ∨ Terminal s := by
  rw [step_none_iff aligned]
  constructor
  · rintro (denied | stopped)
    · rcases frontier_or_admitted wf typed aligned with frontier | allowed
      · exact Or.inl frontier
      · exact False.elim (denied allowed)
    · rcases ANL.Words.stopped_iff.mp stopped with terminal | invalid
      · exact Or.inr terminal
      · exact False.elim (typed.not_invalid invalid)
  · rintro (frontier | terminal)
    · exact Or.inl (primitive_not_admitted frontier)
    · exact Or.inr (ANL.Words.stopped_iff.mpr (Or.inl terminal))

end ANL.Boot.Origin
