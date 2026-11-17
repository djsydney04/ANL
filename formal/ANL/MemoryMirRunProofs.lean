import ANL.MemoryMirRun

namespace ANL.Memory.Mir

private theorem missing_pair {x : Option α} {y : Option β}
    (h : ∀ a b, x = some a → y = some b → False) : x = none ∨ y = none := by
  cases x <;> cases y <;> simp_all

private theorem not_integer {v : Val} (h : ∀ n, v ≠ .scalar (.int n)) :
    v.type ≠ .scalar .i64 := by
  cases v with
  | tuple _ => simp [APL.FlatProducts.Val.type]
  | scalar x => cases x <;> simp_all [APL.FlatProducts.Val.type, APL.Val.type]

private theorem not_boolean {v : Val} (ht : v ≠ .scalar (.bool true))
    (hf : v ≠ .scalar (.bool false)) : v.type ≠ .scalar .bool := by
  cases v with
  | tuple _ => simp [APL.FlatProducts.Val.type]
  | scalar x =>
    cases x with
    | int _ => simp [APL.FlatProducts.Val.type, APL.Val.type]
    | unit => simp [APL.FlatProducts.Val.type, APL.Val.type]
    | bool test => cases test <;> contradiction

private theorem not_unit {v : Val} (h : v ≠ .scalar .unit) : v.type ≠ .scalar .unit := by
  cases v with
  | tuple _ => simp [APL.FlatProducts.Val.type]
  | scalar x => cases x <;> simp_all [APL.FlatProducts.Val.type, APL.Val.type]

theorem step_complete (h : Step p responses s t) : step p responses s = some t := by
  cases h <;> simp_all [step]
  all_goals repeat (split <;> simp_all [CloseReady, APL.FlatProducts.Val.type, APL.Val.type])
  all_goals omega

theorem step_sound (h : step p responses s = some t) : Step p responses s t := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp only [step] at h
  repeat' (split at h)
  all_goals simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals subst t
  all_goals try simp_all only
  all_goals first
    | solve_by_elim (maxDepth := 5) [Or.inl, Or.inr,
    
    Step.block,
    Step.instruction,
    Step.yieldFound,
    Step.yieldMissing,
    Step.integer,
    Step.boolean,
    Step.unit,
    Step.tupleFound,
    Step.tupleMissing,
    Step.projectFound,
    Step.projectMissing,
    Step.unaryFound,
    Step.unaryMissing,
    Step.binaryFound,
    Step.binaryMissing,
    Step.callFound,
    Step.callMissing,
    Step.mutableFound,
    Step.mutableMissing,
    Step.loadFound,
    Step.loadMissing,
    Step.storeValueMissing,
    Step.storeSlotMissing,
    Step.storeSlot,
    Step.whileStart,
    Step.branchTrue,
    Step.branchFalse,
    Step.branchWrong,
    Step.heapFound,
    Step.heapMissing,
    Step.lengthFound,
    Step.lengthMissing,
    Step.readFound,
    Step.readMissing,
    Step.writeFound,
    Step.writeMissing,
    Step.writeDenied,
    Step.viewFound,
    Step.viewMissing,
    Step.viewDenied,
    Step.instructionReturn,
    Step.blockReturn,
    Step.slotReturn,
    Step.slotWrong,
    Step.whileTrue,
    Step.whileFalse,
    Step.whileWrong,
    Step.whileAgain,
    Step.bodyWrong,
    Step.heapInitialReturn,
    Step.heapInitialWrong,
    Step.ownerReturn,
    Step.writeValueReturn,
    Step.writeValueWrong,
    Step.callReturn,
    Step.negativeLength,
    Step.nonnegativeLength,
    Step.lengthWrong,
    Step.allocated,
    Step.allocationRefused,
    Step.allocationRejected,
    Step.readChecked,
    Step.readBounds,
    Step.readWrong,
    Step.readValue,
    Step.readAbsent,
    Step.writeChecked,
    Step.writeBounds,
    Step.writeWrong,
    Step.stored,
    Step.storeAbsent,
    Step.invokeMissing,
    Step.invokeFound,
    Step.invokeWrong,
    Step.grantMissing,
    Step.grantWrong,
    Step.grantFound,
    Step.closeFound,
    Step.closeWrong,
    Step.closeAbsent,
    Step.revoke,
    Step.revokeWrong,
    Step.restore,
    Step.restoreWrong]
    | skip

  all_goals first
    | solve | apply Step.readMissing; exact missing_pair ‹_›
    | solve | apply Step.writeMissing; exact missing_pair ‹_›
    | solve | apply Step.viewMissing; exact missing_pair ‹_›
    | solve | apply Step.slotWrong; intro prior slots; simp_all <;> omega
    | solve | apply Step.whileWrong; exact not_boolean ‹_› ‹_›
    | solve | apply Step.bodyWrong; exact not_unit ‹_›
    | solve | apply Step.heapInitialWrong; exact not_integer ‹_›
    | solve | apply Step.writeValueWrong; exact not_integer ‹_›
    | solve | apply Step.lengthWrong; exact not_integer ‹_›
    | solve | apply Step.readWrong; exact not_integer ‹_›
    | solve | apply Step.writeWrong; exact not_integer ‹_›
    | solve | apply Step.closeAbsent <;> simp_all [CloseReady]
    | solve | apply Step.closeWrong; unfold CloseReady; split <;> simp_all <;> solve_by_elim (maxDepth := 12)

theorem step_iff : step p responses s = some t ↔ Step p responses s t :=
  ⟨step_sound, step_complete⟩

theorem Step.deterministic (h₁ : Step p responses s a) (h₂ : Step p responses s b) : a = b :=
  Option.some.inj ((step_complete h₁).symm.trans (step_complete h₂))

theorem stopped_iff (p : Program) (responses : Responses) (s : State) :
    step p responses s = none ↔ RawStopped s := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp [step, RawStopped]
  cases k <;> simp

theorem isStopped_iff (s : State) : isStopped s = true ↔ RawStopped s := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp [isStopped, RawStopped]

theorem isStopped_step_iff (p : Program) (responses : Responses) (s : State) :
    isStopped s = true ↔ step p responses s = none :=
  (isStopped_iff s).trans (stopped_iff p responses s).symm

theorem Terminal.rawStopped (h : Terminal s) : RawStopped s := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp_all [Terminal, RawStopped]

theorem RawStopped.no_step (h : RawStopped s) : ¬ Step p responses s t := by
  intro hs
  have stopped := (stopped_iff p responses s).mpr h
  rw [step_complete hs] at stopped
  contradiction

theorem Steps.trans (h₁ : Steps p responses s t) (h₂ : Steps p responses t u) :
    Steps p responses s u := by
  induction h₁ with
  | refl => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

theorem run_spec (p : Program) (responses : Responses) (budget : Nat) (s : State) :
    let result := run p responses budget s
    Steps p responses s result.state ∧
      match result with
      | .completed final => RawStopped final
      | .exhausted stopped => ¬ RawStopped stopped := by
  induction budget generalizing s with
  | zero =>
      simp only [run]
      split
      · next hs => exact ⟨.refl, (isStopped_iff s).mp hs⟩
      · next hs => exact ⟨.refl, fun ht => hs ((isStopped_iff s).mpr ht)⟩
  | succ budget ih =>
      cases h : step p responses s with
      | none =>
          simp only [run, h, RunResult.state]
          exact ⟨.refl, (stopped_iff p responses s).mp h⟩
      | some next =>
          simp only [run, h]
          exact ⟨.cons (step_sound h) (ih next).1, (ih next).2⟩

theorem run_completed_sound (h : run p responses budget s = .completed t) :
    Steps p responses s t ∧ RawStopped t := by
  simpa [h, RunResult.state] using run_spec p responses budget s

theorem run_exhausted_prefix (h : run p responses budget s = .exhausted t) :
    Steps p responses s t ∧ ¬ RawStopped t := by
  simpa [h, RunResult.state] using run_spec p responses budget s

theorem run_complete (h : Steps p responses s t) (ht : RawStopped t) :
    ∃ budget, run p responses budget s = .completed t := by
  induction h with
  | refl => exact ⟨0, by simp [run, (isStopped_iff _).mpr ht]⟩
  | cons h _ ih =>
      obtain ⟨budget, hb⟩ := ih ht
      exact ⟨budget + 1, by simp [run, step_complete h, hb]⟩

theorem run_iff : (∃ budget, run p responses budget s = .completed t) ↔
    Steps p responses s t ∧ RawStopped t := by
  constructor
  · rintro ⟨_, h⟩
    exact run_completed_sound h
  · rintro ⟨hs, ht⟩
    exact run_complete hs ht

theorem RawStopped.steps_eq (ht : RawStopped s) (hs : Steps p responses s t) : t = s := by
  cases hs with
  | refl => rfl
  | cons h _ => exact False.elim (ht.no_step h)

theorem bindParameters_length {params : List Temp} {values : List Val}
    (h : bindParameters params values = some bindings) :
    params.length = values.length ∧ bindings.length = params.length := by
  induction params generalizing values bindings with
  | nil =>
      cases values <;> simp_all [bindParameters]
  | cons param params ih =>
      cases values with
      | nil => simp [bindParameters] at h
      | cons value values =>
          simp only [bindParameters, Option.map_eq_some_iff] at h
          obtain ⟨rest, hr, rfl⟩ := h
          have facts := ih hr
          simp [facts.1, facts.2]

theorem bindParameters_ids {params : List Temp} {values : List Val}
    (h : bindParameters params values = some bindings) :
    bindings.map Prod.fst = params.map Temp.id := by
  induction params generalizing values bindings with
  | nil => cases values <;> simp_all [bindParameters]
  | cons param params ih =>
      cases values with
      | nil => simp [bindParameters] at h
      | cons value values =>
          simp only [bindParameters, Option.map_eq_some_iff] at h
          obtain ⟨rest, hr, rfl⟩ := h
          simp [ih hr]

theorem restore_inaccessible (a : Activation) (k : List Frame) (w : World) (value : Val) :
    (State.mk (.restore value) a k w).accessible = [] := rfl

theorem trap_retains_state (h : Steps p responses ⟨.trap kind, a, k, w⟩ t) :
    t = ⟨.trap kind, a, k, w⟩ := RawStopped.steps_eq trivial h

theorem run_zero_allocate (p : Program) (responses : Responses) (site : Site)
    (owner length : Nat) (value : APL.I64) (success failure : Block)
    (a : Activation) (k : List Frame) (w : World) :
    run p responses 0 ⟨.allocate site owner length value success failure, a, k, w⟩ =
      .exhausted ⟨.allocate site owner length value success failure, a, k, w⟩ := rfl

theorem invalid_stopped_not_terminal (a : Activation) (k : List Frame) (w : World) :
    RawStopped ⟨.invalid, a, k, w⟩ ∧ ¬ Terminal ⟨.invalid, a, k, w⟩ := ⟨trivial, id⟩

end ANL.Memory.Mir
