import ANL.WordsRun
import ANL.WordsValueTyping

namespace ANL.Words

open ANL.Memory

theorem step_complete (h : Step p responses s next) : step p responses s = some next := by
  cases h <;> simp_all [step]
  all_goals split <;> simp_all [Val.type, ScalarVal.type, APL.Val.type]
  all_goals split <;> simp_all

theorem bool_canonical {v : Val} (h : v.type = .scalar (.legacy .bool)) :
    ∃ b, v = .scalar (.legacy (.bool b)) := by
  obtain ⟨a, rfl, ha⟩ := scalar_canonical h
  obtain ⟨b, rfl, hb⟩ := scalar_legacy_canonical ha
  cases b <;> simp_all [APL.Val.type]

theorem int_canonical {v : Val} (h : v.type = .scalar (.legacy .i64)) :
    ∃ n, v = .scalar (.legacy (.int n)) := by
  obtain ⟨a, rfl, ha⟩ := scalar_canonical h
  obtain ⟨b, rfl, hb⟩ := scalar_legacy_canonical ha
  cases b <;> simp_all [APL.Val.type]

theorem unit_canonical {v : Val} (h : v.type = .scalar (.legacy .unit)) :
    v = .scalar (.legacy .unit) := by
  obtain ⟨a, rfl, ha⟩ := scalar_canonical h
  obtain ⟨b, rfl, hb⟩ := scalar_legacy_canonical ha
  cases b <;> simp_all [APL.Val.type]

set_option linter.unusedSimpArgs false in
theorem step_sound (h : step p responses s = some next) : Step p responses s next := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp only [step] at h
  all_goals repeat' split at h
  all_goals simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals try contradiction
  all_goals subst next
  all_goals try simp_all only [Bool.not_eq_true]
  all_goals try obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›
  all_goals first
    | solve_by_elim (maxDepth := 6) [Step.word, Step.convertEval, Step.convertReturn, Step.lit, Step.localFound, Step.localMissing, Step.letEval, Step.letMutEval, Step.assignEval, Step.whileEval, Step.ifEval, Step.unaryEval, Step.binaryEval, Step.call, Step.tupleEmpty, Step.tupleFirst, Step.projectEval, Step.heapEval, Step.lengthFound, Step.lengthMissing, Step.readEval, Step.readMissing, Step.writeEval, Step.writeMissing, Step.writeDenied, Step.callView, Step.viewMissing, Step.viewDenied, Step.bindReturn, Step.scopeReturn, Step.scopeMissing, Step.assignReturn, Step.assignMissing, Step.ifTrue, Step.ifFalse, Step.ifWrong, Step.unaryReturn, Step.short, Step.rightEval, Step.binaryReturn, Step.argumentReturn, Step.callResult, Step.whileTrue, Step.whileFalse, Step.whileWrong, Step.whileAgain, Step.bodyWrong, Step.fieldNext, Step.fieldsDone, Step.fieldTuple, Step.projectReturn, Step.heapLengthReturn, Step.heapInitialReturn, Step.heapInitialWrong, Step.ownerReturn, Step.readIndexReturn, Step.writeIndexReturn, Step.writeValueReturn, Step.writeValueWrong, Step.negativeLength, Step.nonnegativeLength, Step.lengthWrong, Step.allocated, Step.allocationRefused, Step.allocationRejected, Step.readChecked, Step.readBounds, Step.readWrong, Step.readValue, Step.readUnavailable, Step.writeChecked, Step.writeBounds, Step.writeWrong, Step.stored, Step.storeUnavailable, Step.invoke, Step.invokeMissing, Step.invokeMode, Step.grant, Step.grantMissing, Step.closed, Step.closeUnavailable, Step.closeWrong, Step.revoke, Step.revokeWrong, Step.restore, Step.restoreWrong]
    | skip
  all_goals first
    | (apply Step.ifWrong; intro ht; obtain ⟨test, rfl⟩ := bool_canonical ht; simp_all)
    | (apply Step.whileWrong; intro ht; obtain ⟨test, rfl⟩ := bool_canonical ht; cases test <;> simp_all)
    | (apply Step.bodyWrong; intro ht; have he := unit_canonical ht; simp_all)
    | (apply Step.heapInitialWrong; intro ht; obtain ⟨value, rfl⟩ := int_canonical ht; simp_all)
    | (apply Step.writeValueWrong; intro ht; obtain ⟨value, rfl⟩ := int_canonical ht; simp_all)
    | (apply Step.lengthWrong; intro ht; obtain ⟨value, rfl⟩ := int_canonical ht; simp_all)
    | (apply Step.readWrong; intro ht; obtain ⟨value, rfl⟩ := int_canonical ht; simp_all)
    | (apply Step.writeWrong; intro ht; obtain ⟨value, rfl⟩ := int_canonical ht; simp_all)
    | (apply Step.closeWrong; intro k he; cases he; simp_all)

theorem step_iff : step p responses s = some next ↔ Step p responses s next :=
  ⟨step_sound, step_complete⟩

theorem deterministic (ha : Step p responses s a) (hb : Step p responses s b) : a = b :=
  Option.some.inj ((step_complete ha).symm.trans (step_complete hb))

theorem terminal_iff {s : State} : Terminal s ↔
    (∃ value, s.control = .ret value ∧ s.kont = []) ∨ ∃ kind, s.control = .trap kind := by
  constructor
  · intro h; cases h
    · exact .inl ⟨_, rfl, rfl⟩
    · exact .inr ⟨_, rfl⟩
  · intro h
    rcases s with ⟨control, a, k, w⟩
    rcases h with ⟨value, rfl, rfl⟩ | ⟨kind, rfl⟩
    · exact .value
    · exact .trap

theorem stopped_iff : step p responses s = none ↔ Terminal s ∨ s.control = .invalid := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp [step, terminal_iff]
  case ret value => cases k <;> simp

theorem isStopped_iff : isStopped s = true ↔ step p responses s = none := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp [isStopped, step]
  case ret value => cases k <;> simp

theorem rawStopped_iff : isStopped s = true ↔ RawStopped s := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp [isStopped, RawStopped, terminal_iff]

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

end ANL.Words
