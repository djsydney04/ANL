import APL.FlatProductsEmbedding

set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace APL.FlatProducts.Examples

private def z : APL.Val := .int ⟨0, by decide⟩
private def one : APL.Val := .int ⟨1, by decide⟩
private def two : APL.Val := .int ⟨2, by decide⟩
private def three : APL.Val := .int ⟨3, by decide⟩
private def num (v : APL.Val) : Term := .lit (.scalar v)
private def pair (a b : APL.Val) : Val := .tuple ⟨[a, b], by simp, by simp⟩
private def pairTy : Ty := .tuple ⟨[.i64, .i64], by decide, by decide⟩
private def tick : Term := .letE (.assign 0 (.binary .add (.local 0) (num one))) (.local 1)

private def capturedFields : Term :=
  .letMut (num z) (.tuple [.local 0, .letE (.assign 0 (num one)) (.local 1)])

private theorem fields_capture_and_effects :
    infer #[] [] capturedFields = some pairTy ∧
    run #[] 40 (.eval capturedFields [] []) = some (.ret (pair z one) [] []) := by
  constructor
  · simp only [capturedFields, num, z, one, infer, Val.type, APL.Val.type, List.mapM_cons, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero, Option.map_some,
      Option.bind_eq_bind, Option.bind_some, true_and, Nat.reduceAdd, List.getElem_cons_succ, List.mapM_nil,
      Option.pure_def, Flat.make, ↓reduceIte, Ty.asScalar, Nat.zero_lt_succ, Nat.reduceLeDiff, and_self, ↓reduceDIte,
      pairTy]
  · rfl


private def projected : Term :=
  .letMut (num z) (.letE (.project (.tuple [tick, tick]) 0)
    (.tuple [.local 0, .local 1]))

private theorem projection_once_evaluates_all_fields :
    infer #[] [] projected = some pairTy ∧
    run #[] 70 (.eval projected [] []) = some (.ret (pair one two) [] []) := by
  constructor
  · simp only [projected, num, z, tick, one, infer, Val.type, APL.Val.type, List.mapM_cons, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero, Option.map_some, binaryType,
      APL.binaryType, reduceCtorEq, or_self, false_and, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, true_and,
      Nat.reduceAdd, List.getElem_cons_succ, List.mapM_nil, Option.pure_def, Flat.make, Nat.zero_lt_succ, Ty.asScalar,
      Nat.reduceLeDiff, and_self, ↓reduceDIte, pairTy]
  · rfl


private def snapshots : Term :=
  .letMut (.tuple [num z, num z])
    (.letE (.local 0)
      (.letE (.assign 1 (.tuple [num one, num one]))
        (.tuple [.project (.local 1) 0, .project (.local 2) 0])))

private theorem whole_assignment_preserves_snapshot :
    infer #[] [] snapshots = some pairTy ∧
    run #[] 80 (.eval snapshots [] []) = some (.ret (pair z one) [] []) := by
  constructor
  · simp only [snapshots, num, z, one, infer, List.mapM_cons, Val.type, APL.Val.type, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, Flat.make, Ty.asScalar, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, Nat.reduceLeDiff, and_self, ↓reduceDIte, Nat.lt_add_one,
      getElem?_pos, List.getElem_cons_zero, Option.map_some, List.getElem_cons_succ, true_and, Nat.reduceLT, ↓reduceIte,
      pairTy]
  · rfl


private def equalityEffects : Term :=
  .letMut (num z)
    (.letE (.binary .eq (.tuple [tick]) (.tuple [tick]))
      (.tuple [.local 0, .local 1]))

private theorem equality_runs_both_operands :
    run #[] 80 (.eval equalityEffects [] []) = some (.ret (pair (.bool false) two) [] []) := rfl

private def badDivision : Term := .binary .div (num one) (num z)
private def overflow : Term := .binary .add (.lit (.scalar (.int ⟨maxI64, by decide⟩))) (num one)

private theorem projection_does_not_skip_later_trap :
    run #[] 40 (.eval (.project (.tuple [num one, badDivision]) 0) [] []) =
      some (.trap .divisionByZero) := rfl

private theorem first_field_trap_precedes_later_trap :
    run #[] 40 (.eval (.tuple [badDivision, overflow]) [] []) =
      some (.trap .divisionByZero) := rfl

private def calling : Functions := #[
  ⟨"modify_copy", [pairTy, .scalar .i64], pairTy,
    .letMut (.local 1) (.letE (.assign 0 (.tuple [.local 1, .local 1])) (.local 1))⟩]

private def caller : Term :=
  .letMut (.tuple [num z, num z])
    (.letE (.call 0 [.local 0,
      .letE (.assign 0 (.tuple [num one, num one])) (num two)])
      (.tuple [.project (.local 0) 0, .project (.local 1) 0]))

private theorem tuple_call_isolates_caller_after_argument_effects :
    infer (signatures calling) [] caller = some pairTy ∧
    run calling 100 (.eval caller [] []) = some (.ret (pair two one) [] []) := by
  constructor
  · simp only [signatures, calling, pairTy, List.map_toArray, List.map_cons, List.map_nil, caller, num, z, one,
      two, infer, List.mapM_cons, Val.type, APL.Val.type, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Flat.make, Ty.asScalar, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
      Nat.zero_lt_succ, Nat.reduceLeDiff, and_self, ↓reduceDIte, List.size_toArray, Nat.lt_add_one, getElem?_pos,
      List.getElem_toArray, List.getElem_cons_zero, Option.map_some, true_and, List.getElem_cons_succ, ↓reduceIte]
  · rfl


private def capturedCall : Functions := #[
  ⟨"keep_first", [pairTy, .scalar .i64], pairTy, .local 1⟩]

private theorem tuple_argument_is_captured_before_later_mutation :
    run capturedCall 100 (.eval caller [] []) = some (.ret (pair z one) [] []) := rfl

private def singletonTy : Ty := .tuple ⟨[.i64], by decide, by decide⟩
private def recursive : Functions := #[
  ⟨"count_down", [.scalar .i64], singletonTy,
    .ifE (.binary .eq (.local 0) (num z)) (.tuple [num z])
      (.call 0 [.binary .sub (.local 0) (num one)])⟩]

private theorem recursive_table_typed : WellTyped recursive := by
  apply checked_functions
  intro f fn hf
  cases f with
  | zero =>
    simp [recursive] at hf
    subst fn
    simp only [signatures, recursive, singletonTy, num, z, one, List.map_toArray, List.map_cons, List.map_nil,
      immutable, List.reverse_cons, List.reverse_nil, List.nil_append, infer, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero, Option.map_some, Val.type, APL.Val.type,
      binaryType, APL.binaryType, Option.map_ite, reduceCtorEq, or_false, true_and, Option.bind_eq_bind, Option.bind_some,
      ↓reduceIte, List.mapM_cons, List.mapM_nil, Option.pure_def, Flat.make, Ty.asScalar, Nat.reduceLeDiff, and_self,
      ↓reduceDIte, List.size_toArray, List.getElem_toArray, or_self, false_and, and_true]
  | succ f => simp [recursive] at hf


private theorem recursive_tuple_return :
    run recursive 150 (.eval (.call 0 [num three]) [] []) =
      some (.ret (.tuple ⟨[z], by decide, by decide⟩) [] []) := rfl

private def loopState : Term :=
  .letMut (.tuple [num z, .lit (.scalar (.bool false))])
    (.letE (.whileE (.binary .lt (.project (.local 0) 0) (num two))
      (.assign 0 (.tuple [.binary .add (.project (.local 0) 0) (num one),
        .lit (.scalar (.bool true))]))) (.local 1))

private theorem tuple_loop_replaces_whole_value :
    run #[] 150 (.eval loopState [] []) = some (.ret (pair two (.bool true)) [] []) := rfl

private theorem singleton_unit_distinct :
    infer #[] [] (.tuple [.lit (.scalar .unit)]) =
      some (.tuple ⟨[.unit], by decide, by decide⟩) ∧
    infer #[] [] (.lit (.scalar .unit)) = some (.scalar .unit) := by
  constructor
  · simp only [infer, List.mapM_cons, Val.type, APL.Val.type, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Flat.make, Ty.asScalar, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one,
      Nat.reduceLeDiff, and_self, ↓reduceDIte]
  · simp only [infer, Val.type, APL.Val.type]


private theorem width_boundaries :
    infer #[] [] (.tuple (List.replicate 8 (num z))) =
      some (.tuple ⟨List.replicate 8 .i64, by decide, by decide⟩) ∧
    infer #[] [] (.tuple (List.replicate 9 (num z))) = none ∧
    infer #[] [] (.tuple []) = none := by
  constructor
  · simp only [num, z, List.reduceReplicate, infer, List.mapM_cons, Val.type, APL.Val.type, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, Flat.make, Ty.asScalar, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, Std.le_refl, and_self, ↓reduceDIte]
  constructor
  · simp only [num, z, List.reduceReplicate, infer, List.mapM_cons, Val.type, APL.Val.type, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, Flat.make, Ty.asScalar, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, Nat.reduceLeDiff, and_false, ↓reduceDIte, Option.bind_none]
  · simp only [infer, List.mapM_nil, Option.pure_def, Flat.make, Option.bind_eq_bind, Option.bind_some,
      List.length_nil, Nat.lt_irrefl, Nat.zero_le, and_true, ↓reduceDIte, Option.bind_none]


private theorem raw_illtyped_terms_remain_representable :
    infer #[] [] (.tuple [.tuple [num z]]) = none ∧
    run #[] 20 (.eval (.tuple [.tuple [num z]]) [] []) = some .invalid ∧
    infer #[] [] (.project (.tuple [num z]) 1) = none ∧
    run #[] 20 (.eval (.project (.tuple [num z]) 1) [] []) = some .invalid ∧
    infer #[] [] (.binary .eq (.tuple [num z]) (.tuple [.lit (.scalar (.bool true))])) = none := by
  constructor
  · simp only [num, z, infer, List.mapM_cons, Val.type, APL.Val.type, List.mapM_nil, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, Flat.make, Ty.asScalar, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.lt_add_one, Nat.reduceLeDiff, and_self, ↓reduceDIte, Option.bind_none]
  constructor
  · rfl
  constructor
  · simp only [num, z, infer, List.mapM_cons, Val.type, APL.Val.type, List.mapM_nil, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, Flat.make, Ty.asScalar, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.lt_add_one, Nat.reduceLeDiff, and_self, ↓reduceDIte, Nat.lt_irrefl, not_false_eq_true, getElem?_neg,
      Option.map_none]
  constructor
  · rfl
  · simp only [num, z, infer, List.mapM_cons, Val.type, APL.Val.type, List.mapM_nil, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, Flat.make, Ty.asScalar, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.lt_add_one, Nat.reduceLeDiff, and_self, ↓reduceDIte, binaryType, APL.binaryType, Option.map_ite, reduceCtorEq,
      or_false, true_and, Flat.mk.injEq, List.cons.injEq, and_true, ↓reduceIte]


private theorem tuple_machine_safety_instance :
    ∀ last, Steps recursive (.eval (.call 0 [num three]) [] []) last →
      last.Typed (signatures recursive) singletonTy ∧
      (Terminal last ∨ ∃ next, Step recursive last next) := by
  intro last hs
  apply safety recursive_table_typed (hs := hs)
  exact .eval (infer_sound (by
    simp only [signatures, recursive, singletonTy, num, z, one, List.map_toArray, List.map_cons, List.map_nil,
      three, infer, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
      List.getElem_toArray, List.getElem_cons_zero, List.mapM_cons, Val.type, APL.Val.type, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, ↓reduceIte])) (Γ := []) rfl .nil


end APL.FlatProducts.Examples

namespace APL.FlatProducts.Examples.Boundaries

private def truth : Term := .lit (.scalar (.bool true))
private def unit : Term := .lit (.scalar .unit)
private def forever : Term := .whileE truth unit
private def zero : APL.Val := .int ⟨0, by decide⟩
private def one : APL.Val := .int ⟨1, by decide⟩
private def divideZero : Term := .binary .div (.lit (.scalar one)) (.lit (.scalar zero))
private def shape : Flat APL.Ty := ⟨[.unit, .i64], by decide, by decide⟩
private def suspendedTuple : Term := .tuple [forever, divideZero]

private theorem cycle_run (budget : Nat) (env : Env) (k : List Frame) :
    run #[] budget (.eval truth env (.condition truth unit :: k)) = none := by
  induction budget using Nat.strongRecOn with
  | ind budget ih =>
    rcases budget with _ | (_ | (_ | (_ | budget)))
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ih budget (by omega)

private theorem suspended_typed : HasType #[] [] suspendedTuple (.tuple shape) := by
  apply HasType.tuple
  exact .cons (.whileE .lit .lit) (.cons (.binary .lit .lit (by rfl)) .nil)

private theorem typed_divergent_field_never_reaches_later_trap :
    HasType #[] [] suspendedTuple (.tuple shape) ∧
    (∀ budget, run #[] budget (.eval suspendedTuple [] []) = none) ∧
    (∀ last, Steps #[] (.eval suspendedTuple [] []) last →
      last.Typed (signatures #[]) (.tuple shape) ∧
      (Terminal last ∨ ∃ next, Step #[] last next)) := by
  refine ⟨suspended_typed, ?_, ?_⟩
  · intro budget
    rcases budget with _ | (_ | budget)
    · rfl
    · rfl
    · exact cycle_run budget [] [.fields [divideZero] []]
  · intro last hs
    have wf : WellTyped (#[] : Functions) := by intro f fn h; simp at h
    have start : State.Typed (signatures #[]) (.eval suspendedTuple [] []) (.tuple shape) :=
      .eval (by simpa [signatures] using suspended_typed) (Γ := []) rfl .nil
    exact safety wf start hs

private theorem prior_trap_precedes_divergent_field :
    run #[] 20 (.eval (.tuple [divideZero, forever]) [] []) =
      some (.trap .divisionByZero) := rfl

private def oldTuple : Val := .tuple ⟨[.bool false], by decide, by decide⟩
private def newTuple : Val := .tuple ⟨[.bool true], by decide, by decide⟩
private def falseEffect : Term :=
  .letMut (.lit oldTuple)
    (.letE (.whileE (.letE (.assign 0 (.lit newTuple)) (.lit (.scalar (.bool false)))) unit)
      (.local 1))

private theorem false_guard_keeps_whole_tuple_update :
    infer #[] [] falseEffect = some newTuple.type ∧
    run #[] 30 (.eval falseEffect [] []) = some (.ret newTuple [] []) := by
  constructor
  · simp [falseEffect, oldTuple, newTuple, unit, infer, Val.type, Flat.map, APL.Val.type]
  · rfl

private def malformedTable : Functions := #[⟨"bad_body", [], .scalar .unit, .local 0⟩]

private theorem well_typed_table_premise_is_necessary :
    State.Typed (signatures malformedTable) (.invoke 0 [] [] []) (.scalar .unit) ∧
    (¬ WellTyped malformedTable) ∧
    run malformedTable 3 (.invoke 0 [] [] []) = some .invalid := by
  refine ⟨entry_typed (fs := malformedTable) (f := 0) (fn := ⟨"bad_body", [], .scalar .unit, .local 0⟩)
    (by rfl) (by rfl), ?_, rfl⟩
  intro wf
  have body := wf 0 _ (by rfl)
  have inferred := infer_complete body
  simp [malformedTable, immutable, infer] at inferred

end APL.FlatProducts.Examples.Boundaries
