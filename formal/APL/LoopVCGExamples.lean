import APL.LoopVCGContracts
import APL.LoopVCGQueries

/-! Kernel-checked discriminators for model invariant generation, support,
contracts, and actual machine behavior. These examples do not establish
production loop verification or source-to-model correspondence. -/

namespace APL.LoopVCG.Examples.Generator

open VCG
private def noRequires : Preconditions := fun _ => []
private def trueLoop : LoopAnnotations.Term :=
  .whileE [.lit (.bool true)] (.lit (.bool true)) (.lit .unit)

example : (analyze #[] noRequires 4 [] trueLoop [] (.truth true) 0).isSome = true := by
  simp [analyze, trueLoop, LocalState.infer, LoopAnnotations.signatures, LoopAnnotations.Term.erase]
  rfl
example : (analyze #[] noRequires 4 []
    (.whileE [] (.lit (.bool false)) (.lit .unit)) [] (.truth true) 0).isNone = true := by
  simp [analyze, LocalState.infer, LoopAnnotations.signatures, LoopAnnotations.Term.erase]
example : (analyze #[] noRequires 4 [(.i64, true)]
    (.whileE [.lit (.bool true)] (.lit (.bool false)) (.lit .unit))
    [.var 0] (.truth true) 1).map Analysis.next = some 2 := by
  simp [analyze, LocalState.infer, LoopAnnotations.signatures, LoopAnnotations.Term.erase]
  rfl

end APL.LoopVCG.Examples.Generator

namespace APL.LoopVCG.Examples.ArtifactSupport

open VCG
-- Independent boundary witnesses: an out-of-range name must not pass support.
example : ¬ Supported Below (single (.var 5) [] (.truth true) 5) := by
  intro h
  have bound := (h.1 ⟨.var 5, [], .truth true⟩ (by simp [single])).1
  exact Nat.lt_irrefl 5 bound

private def never : LoopAnnotations.Term :=
  .whileE [.lit (.bool true)] (.lit (.bool false)) (.lit .unit)

private def nestedFunctions : LoopAnnotations.Functions := #[{
  name := "copy_then_loop", params := [.i64], result := .unit,
  body := .letMut (.local 0) never
}]

private def nestedArguments : LoopAnnotations.Term :=
  .call 0 [.letE never (.local 1)]

-- The argument's mutable head gets identity 1; the callee's copy gets 2. The
-- returned caller environment keeps the argument head, not the callee copy.
set_option maxHeartbeats 2000000 in
example : (analyze nestedFunctions (fun _ => []) 4 [(.i64, true)] nestedArguments
    [.var 0] (.truth true) 1).map (fun a => (a.next, a.outcomes.map Outcome.env)) =
    some (3, [[.var 1]]) := by
  simp (config := { maxSteps := 200000 }) [analyze, nestedFunctions, nestedArguments, never, arguments,
    LocalState.infer, LoopAnnotations.signatures, LoopAnnotations.Term.erase,
    bindAnalysis, sequence, single, combine, addCheck]
  rfl

example (h : analyze nestedFunctions (fun _ => []) 4 [(.i64, true)] nestedArguments
    [.var 0] (.truth true) 1 = some a) : Supported Below a :=
  analyze_supported h ⟨by change 0 < 1; decide, trivial⟩ trivial

end APL.LoopVCG.Examples.ArtifactSupport

namespace APL.LoopVCG.Examples.AssertionSoundness

open VCG LoopAnnotations
private def undefinedClause : Assertion :=
  .binary .eq (.binary .div (.lit (.int 1)) (.lit (.int 0))) (.lit (.int 0))

private def shortClause : Assertion := .binary .or (.lit (.bool true)) undefinedClause
private def model : Model := fun _ => .unit

private def generated (path : Formula) (clauses : List Assertion) : List Check × Formula :=
  (assertions [] path clauses).getD ([], .truth false)

example : shortClause.eval [] = some (.bool true) := rfl

example : ¬ InvariantsHold [] [undefinedClause] := by
  simp [InvariantsHold, undefinedClause, Assertion.eval, mShort, mBinary]

example : (group (generated (.truth false) [undefinedClause]).1).Holds model := by
  apply (assertions_group_exact (syms := []) (path := .truth false)
    (clauses := [undefinedClause]) (checks := (generated (.truth false) [undefinedClause]).1)
    (truth := (generated (.truth false) [undefinedClause]).2) (by rfl)).mpr
  intro impossible
  exact Bool.noConfusion impossible

example : ¬ (group (generated (.truth true) [undefinedClause]).1).Holds model := by
  intro accepted
  have established := assertions_established
    (syms := []) (path := .truth true) (clauses := [undefinedClause])
    (checks := (generated (.truth true) [undefinedClause]).1)
    (truth := (generated (.truth true) [undefinedClause]).2)
    (by rfl) (EnvRep.nil : EnvRep model [] []) accepted rfl
  simp [InvariantsHold, undefinedClause, Assertion.eval, mShort, mBinary] at established

example : ∃ check,
    (generated (.truth true) [.lit (.bool false), undefinedClause]).1[1]? = some check ∧
    check.guard.Holds model ∧ ¬ check.required.Holds model := by
  refine ⟨_, rfl, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, mShort, mBinary]

end APL.LoopVCG.Examples.AssertionSoundness

namespace APL.LoopVCG.Examples.CallSoundness

open VCG
open LocalState.LoopVerification
private def number (n : Int) (h : InRange n := by decide) : Val := .int ⟨n, h⟩
private def integer (n : Int) (h : InRange n := by decide) : LocalState.Term := .lit (number n h)

private def orderedCallee : LocalState.Function := {
  name := "capture",
  params := [.i64, .i64], result := .i64,
  body := .letMut (.local 1) (.letE (.assign 0 (integer 9))
    (.binary .add (.binary .mul (.local 3) (integer 10)) (.local 2)))
}

private def orderedCall : LocalState.Term := .call 0 [
  .letE (.assign 0 (integer 1)) (.local 1),
  .letE (.assign 0 (integer 2)) (.local 1)
]

-- Earlier arguments are captured before later writes. Callee-local writes do
-- not replace the caller environment saved after the final argument.
example : LocalState.run #[orderedCallee] 100
    (.eval orderedCall [number 0] []) = some (.ret (number 12) [number 2] []) := by rfl

example : LocalState.HasType (LocalState.signatures #[orderedCallee]) [(.i64, true)] orderedCall .i64 := by
  apply LocalState.infer_sound
  simp [LocalState.infer, LocalState.signatures, orderedCallee, orderedCall, integer, number, Val.type]

example : LocalState.WellTyped #[orderedCallee] := by
  apply LocalState.checked_functions
  intro f fn hf
  cases f with
  | zero =>
    simp at hf
    subst fn
    simp [orderedCallee, LocalState.signatures, LocalState.immutable, integer, number,
      LocalState.infer, Val.type, binaryType]
  | succ f => simp at hf

-- A false requires clause remains a failed guarded obligation even if its body
-- would otherwise return safely.
example : ¬ ValidFrom 0 (fun _ => .unit)
    (addCheck (.truth true) (.and (.truth true) (.holds (.lit (.bool false))))
      (single (SymTerm.lit .unit) [] (.truth true) 0)).checks := by
  intro h
  have failed := valid_member h
    (check := ⟨.truth true, .and (.truth true) (.holds (.lit (.bool false)))⟩)
    (by simp [addCheck]) agree_refl rfl
  simp [Formula.Holds, SymTerm.eval] at failed

end APL.LoopVCG.Examples.CallSoundness

namespace APL.LoopVCG.Examples.ContractSoundness

open VCG
open LocalState.LoopVerification
private def noPreconditions : Preconditions := fun _ => []
private def forever : LoopAnnotations.Term :=
  .whileE [.lit (.bool true)] (.lit (.bool true)) (.lit .unit)
private def fallback : ContractVC := ⟨.truth false, .truth false, ⟨[], [], 0⟩, []⟩
private def foreverVC : ContractVC :=
  (generateContract #[] noPreconditions 3 [] forever [] (.lit (.bool false))).getD fallback

private theorem forever_generated :
    generateContract #[] noPreconditions 3 [] forever [] (.lit (.bool false)) = some foreverVC := by
  simp [foreverVC, generateContract, forever, parameterSymbols, requiresVC,
    analyze, Val.type, embed, LocalState.immutable, LocalState.infer, LoopAnnotations.signatures,
    LoopAnnotations.Term.erase, freshHead, freshEnv, headDomain, assertions,
    LoopAnnotations.Assertion.instantiate, LoopAnnotations.Assertion.toSpec,
    Spec.instantiate, single, bindAnalysis, sequence, combine, addCheck, postCheck]

private theorem forever_accepted : Accepted [] foreverVC := by
  constructor
  · intro params _
    simp [foreverVC, generateContract, forever, parameterSymbols, requiresVC,
      analyze, Val.type, embed, LocalState.immutable, LocalState.infer, LoopAnnotations.signatures,
      LoopAnnotations.Term.erase, freshHead, freshEnv, headDomain, assertions,
      LoopAnnotations.Assertion.instantiate, LoopAnnotations.Assertion.toSpec,
      Spec.instantiate, single, bindAnalysis, sequence, combine, addCheck, postCheck, Formula.Holds]
  constructor
  · refine ⟨[], rfl, ?_⟩
    simp [foreverVC, generateContract, forever, parameterSymbols, requiresVC,
      analyze, Val.type, embed, LocalState.immutable, LocalState.infer, LoopAnnotations.signatures,
      LoopAnnotations.Term.erase, freshHead, freshEnv, headDomain, assertions,
      LoopAnnotations.Assertion.instantiate, LoopAnnotations.Assertion.toSpec,
      Spec.instantiate, single, bindAnalysis, sequence, combine, addCheck, postCheck, Formula.Holds]
  · intro params _ _ extended _
    simp [foreverVC, generateContract, forever, parameterSymbols, requiresVC,
      analyze, Val.type, embed, LocalState.immutable, LocalState.infer, LoopAnnotations.signatures,
      LoopAnnotations.Term.erase, freshHead, freshEnv, headDomain, assertions,
      LoopAnnotations.Assertion.instantiate, LoopAnnotations.Assertion.toSpec,
      Spec.instantiate, single, bindAnalysis, sequence, combine, addCheck, postCheck,
      group, Formula.Holds, SymTerm.eval, mUnary]

example : ∃ vc, generateContract #[] noPreconditions 3 [] forever [] (.lit (.bool false)) = some vc ∧
    Accepted [] vc := ⟨foreverVC, forever_generated, forever_accepted⟩

private theorem forever_typed : LoopAnnotations.HasType (LoopAnnotations.signatures #[])
    (LocalState.immutable [].reverse) forever .unit := by
  apply LoopAnnotations.HasType.whileE (by simp)
  · intro clause member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst clause
    exact .lit
  · exact .lit
  · exact .lit

-- Accepted false postconditions do not provide a returned-value existence claim.
example : ¬ LocalState.Steps (LoopAnnotations.eraseFunctions #[])
    (.eval forever.erase [] []) (.ret value final []) := by
  intro trace
  have proved := contract_steps_value (params := []) forever_generated forever_accepted
    (by intro f fn hf; simp at hf) forever_typed rfl (by trivial) trace
  simp [Spec.eval] at proved

private def value (n : Int) (h : InRange n := by decide) : Val := .int ⟨n, h⟩
private def num (n : Int) (h : InRange n := by decide) : LoopAnnotations.Term := .lit (value n h)
private def effectfulGuard : LoopAnnotations.Term :=
  .letE (.assign 0 (.binary .add (.local 0) (num 1)))
    (.binary .le (.local 1) (num 2))
private def effectfulLoop : LoopAnnotations.Term :=
  .whileE [.binary .le (.local 0) (.lit (.int 2))] effectfulGuard (.lit .unit)
private def falseExit : LoopAnnotations.Term :=
  .letMut (num 0) (.letE effectfulLoop (.local 1))

-- This machine witness checks the final false guard independently of acceptance.
example : LocalState.run #[] 110 (.eval falseExit.erase [] []) =
    some (.ret (value 3) [] []) := by
  simp only [falseExit, effectfulLoop, effectfulGuard, num, LoopAnnotations.Term.erase]
  rfl
example : (LoopAnnotations.Assertion.binary .le (.local 0) (.lit (.int 2))).eval [.int 3] =
    some (.bool false) := rfl

private def undefinedBoolean : Spec :=
  .binary .eq (.binary .div (.lit (.int 1)) (.lit (.int 0))) (.lit (.int 0))

-- Ordered requires definedness does not inspect a tail behind a false clause.
example : ∃ defined truth, requiresVC [] [.lit (.bool false), undefinedBoolean] =
    some (defined, truth) ∧ defined.Holds (modelOf []) ∧ ¬ truth.Holds (modelOf []) := by
  refine ⟨_, _, rfl, ?_, ?_⟩ <;>
    simp [Formula.Holds, SymTerm.eval, mBinary, mShort]

-- It does inspect an undefined leading clause, even when a later clause is false.
example : ∃ defined truth, requiresVC [] [undefinedBoolean, .lit (.bool false)] =
    some (defined, truth) ∧ ¬ defined.Holds (modelOf []) := by
  refine ⟨_, _, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, mBinary, mShort]

end APL.LoopVCG.Examples.ContractSoundness

namespace APL.LoopVCG.Examples.QueryPartition

open VCG
private def checks : List Check :=
  [⟨.truth false, .truth false⟩, ⟨.truth true, .truth false⟩]

example : (queryKeys (tagFrom (fun _ => 0) 0 checks)) = [0] := rfl
example : (queryChecks 0 (tagFrom (fun _ => 0) 0 checks)).length = 2 := rfl

example : ¬ (∀ query ∈ queries (tagFrom (fun i => i) 0 checks), query.2.Holds model) := by
  rw [tagged_partition_exact]
  simp [checks, group, Formula.Holds]

end APL.LoopVCG.Examples.QueryPartition

namespace APL.LoopVCG.Examples.Machine

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

open VCG

private def model : Model := fun _ => .unit
private def emptyPre : Preconditions := fun _ => []
private def fallback : Analysis SymTerm := single (.lit .unit) [] (.truth false) 0
private theorem empty_wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions #[]) := by
  intro index fn lookup
  simp [LoopAnnotations.eraseFunctions] at lookup

private def divergence : LoopAnnotations.Term :=
  .whileE [.lit (.bool true)] (.lit (.bool true)) (.lit .unit)
private def divergenceAnalysis : Analysis SymTerm :=
  (analyze #[] emptyPre 3 [] divergence [] (.truth true) 0).getD fallback

private theorem divergence_generated :
    analyze #[] emptyPre 3 [] divergence [] (.truth true) 0 = some divergenceAnalysis := by
  simp [divergenceAnalysis, divergence, analyze, LocalState.infer,
    LoopAnnotations.signatures, LoopAnnotations.Term.erase, Val.type]
  rfl

private theorem divergence_valid : ValidFrom 0 model divergenceAnalysis.checks := by
  intro extended _
  simp [divergenceAnalysis, divergence, analyze, LocalState.infer,
    LoopAnnotations.signatures, LoopAnnotations.Term.erase, Val.type,
    LoopAnnotations.Assertion.instantiate, LoopAnnotations.Assertion.toSpec,
    Spec.instantiate, assertions, freshHead, freshEnv, headDomain, single,
    bindAnalysis, sequence, combine, addCheck, group, Formula.Holds, SymTerm.eval,
    embed]

private theorem safe_divergence_every_budget (budget : Nat) :
    LocalState.run #[] budget (.eval divergence.erase [] []) = none := by
  have safe := analyze_run_sound (budget := budget) empty_wf divergence_generated
    (by trivial) (by trivial) (EnvRep.nil : EnvRep model [] []) rfl rfl divergence_valid
  simp only [LoopAnnotations.eraseFunctions, Array.map_empty] at safe
  cases hr : LocalState.run #[] budget (.eval divergence.erase [] []) with
  | none => rfl
  | some last =>
    change StateVCG.RunSafe (Covered 0 model divergenceAnalysis)
      (LocalState.run #[] budget (.eval divergence.erase [] [])) at safe
    rw [hr] at safe
    cases last with
    | eval _ _ _ | invoke _ _ _ _ | trap _ | invalid => exact False.elim safe
    | ret value final k =>
      cases k with
      | cons _ _ => exact False.elim safe
      | nil =>
        simp [StateVCG.RunSafe, Covered, divergenceAnalysis, divergence, analyze,
          LocalState.infer, LoopAnnotations.signatures, LoopAnnotations.Term.erase,
          Val.type, LoopAnnotations.Assertion.instantiate,
          LoopAnnotations.Assertion.toSpec, Spec.instantiate, assertions,
          freshHead, freshEnv, headDomain, single, bindAnalysis, sequence,
          combine, addCheck, Formula.Holds, SymTerm.eval, embed, mUnary] at safe

private def falseEffect : LoopAnnotations.Term :=
  .whileE [.lit (.bool true)]
    (.letE (.assign 0 (.lit (.bool false))) (.local 1)) (.lit .unit)
private def effectAnalysis : Analysis SymTerm :=
  (analyze #[] emptyPre 5 [(.bool, true)] falseEffect [.lit (.bool true)]
    (.truth true) 0).getD fallback

private theorem effect_generated :
    analyze #[] emptyPre 5 [(.bool, true)] falseEffect [.lit (.bool true)]
      (.truth true) 0 = some effectAnalysis := by
  simp [effectAnalysis, falseEffect, analyze, LocalState.infer,
    LoopAnnotations.signatures, LoopAnnotations.Term.erase, Val.type]
  rfl

private theorem effect_valid : ValidFrom 0 model effectAnalysis.checks := by
  intro extended _
  simp [effectAnalysis, falseEffect, analyze, LocalState.infer,
    LoopAnnotations.signatures, LoopAnnotations.Term.erase, Val.type,
    LoopAnnotations.Assertion.instantiate, LoopAnnotations.Assertion.toSpec,
    Spec.instantiate, assertions, freshHead, freshEnv, headDomain, typeGuard,
    single, bindAnalysis, sequence, combine, addCheck, StateVCG.updateSymbols,
    group, Formula.Holds, SymTerm.eval, embed]

private theorem final_false_guard_effect :
    LocalState.run #[] 20 (.eval falseEffect.erase [.bool true] []) =
      some (.ret .unit [.bool false] []) ∧
    Covered 0 model effectAnalysis .unit [.bool false] := by
  have actual : LocalState.run #[] 20 (.eval falseEffect.erase [.bool true] []) =
      some (.ret .unit [.bool false] []) := by
    simp [LocalState.run, LocalState.step, falseEffect, LoopAnnotations.Term.erase,
      LocalState.update]
  refine ⟨actual, ?_⟩
  have safe := analyze_run_sound (budget := 20) empty_wf effect_generated
    (by trivial) (by trivial)
    (EnvRep.cons rfl EnvRep.nil : EnvRep model [.lit (.bool true)] [.bool true])
    rfl rfl effect_valid
  simp only [LoopAnnotations.eraseFunctions, Array.map_empty] at safe
  change StateVCG.RunSafe (Covered 0 model effectAnalysis)
    (LocalState.run #[] 20 (.eval falseEffect.erase [.bool true] [])) at safe
  simpa only [actual, StateVCG.RunSafe] using safe

private def zero : Val := .int ⟨0, by decide⟩
private def one : Val := .int ⟨1, by decide⟩
private def trapBeforeDivergence : LoopAnnotations.Term :=
  .letE (.binary .div (.lit one) (.lit zero)) divergence
private def trapAnalysis : Analysis SymTerm :=
  (analyze #[] emptyPre 5 [] trapBeforeDivergence [] (.truth true) 0).getD fallback

private theorem trap_generated :
    analyze #[] emptyPre 5 [] trapBeforeDivergence [] (.truth true) 0 =
      some trapAnalysis := by
  simp [trapAnalysis, trapBeforeDivergence, divergence, one, zero, analyze,
    LocalState.infer, LoopAnnotations.signatures, LoopAnnotations.Term.erase,
    binaryType, Val.type]
  rfl

private theorem finite_prefix_trap_rejected :
    LocalState.run #[] 20 (.eval trapBeforeDivergence.erase [] []) =
      some (.trap .divisionByZero) ∧ ¬ ValidFrom 0 model trapAnalysis.checks := by
  have actual : LocalState.run #[] 20 (.eval trapBeforeDivergence.erase [] []) =
      some (.trap .divisionByZero) := by
    simp [LocalState.run, LocalState.step, trapBeforeDivergence, divergence,
      LoopAnnotations.Term.erase, one, zero, binary, division, shortCircuit, LocalState.resume]
  refine ⟨actual, ?_⟩
  intro valid
  have safe := analyze_run_sound (budget := 20) empty_wf trap_generated
    (by trivial) (by trivial) (EnvRep.nil : EnvRep model [] []) rfl rfl valid
  simp only [LoopAnnotations.eraseFunctions, Array.map_empty] at safe
  change StateVCG.RunSafe (Covered 0 model trapAnalysis)
    (LocalState.run #[] 20 (.eval trapBeforeDivergence.erase [] [])) at safe
  simp only [actual, StateVCG.RunSafe] at safe

private def nestedCallee : LoopAnnotations.Function := {
  name := "saved-first", params := [.bool, .bool], result := .bool,
  body := .local 1
}
private def nestedFunctions : LoopAnnotations.Functions := #[nestedCallee]
private def nestedCall : LoopAnnotations.Term :=
  .call 0 [.local 0, .letE falseEffect (.local 1)]
private def nestedAnalysis : Analysis SymTerm :=
  (analyze nestedFunctions emptyPre 6 [(.bool, true)] nestedCall [.lit (.bool true)]
    (.truth true) 0).getD fallback

private theorem nested_generated :
    analyze nestedFunctions emptyPre 6 [(.bool, true)] nestedCall [.lit (.bool true)]
      (.truth true) 0 = some nestedAnalysis := by
  cbv

private theorem nested_wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions nestedFunctions) := by
  apply LocalState.checked_functions
  intro index fn lookup
  cases index with
  | zero =>
    simp [nestedFunctions, LoopAnnotations.eraseFunctions] at lookup
    subst fn
    simp [nestedCallee, nestedFunctions, LoopAnnotations.Function.erase,
      LoopAnnotations.eraseFunctions, LoopAnnotations.Term.erase, LocalState.infer,
      LocalState.signatures, LocalState.immutable]
  | succ index => simp [nestedFunctions, LoopAnnotations.eraseFunctions] at lookup

private theorem nested_valid : ValidFrom 0 model nestedAnalysis.checks := by
  intro extended _
  cbv
  simp [Formula.Holds, SymTerm.eval]

private theorem nested_argument_loop_preserves_capture_and_caller :
    LocalState.run (LoopAnnotations.eraseFunctions nestedFunctions) 100
      (.eval nestedCall.erase [.bool true] []) = some (.ret (.bool true) [.bool false] []) ∧
    Covered 0 model nestedAnalysis (.bool true) [.bool false] := by
  have actual : LocalState.run (LoopAnnotations.eraseFunctions nestedFunctions) 100
      (.eval nestedCall.erase [.bool true] []) = some (.ret (.bool true) [.bool false] []) := by
    simp [nestedFunctions, nestedCallee, nestedCall, falseEffect,
      LoopAnnotations.eraseFunctions, LoopAnnotations.Function.erase,
      LoopAnnotations.Term.erase, LocalState.run, LocalState.step, LocalState.update]
  refine ⟨actual, ?_⟩
  exact analyze_steps_value nested_wf nested_generated
    (by trivial) (by trivial)
    (EnvRep.cons rfl EnvRep.nil : EnvRep model [.lit (.bool true)] [.bool true])
    rfl rfl nested_valid (LocalState.run_sound actual).1

private theorem arbitrary_query_grouping_keeps_prefix_trap (classify : Nat → Nat) (first : Nat) :
    ¬ LoopVCG.QueriesValidFrom classify first 0 model trapAnalysis.checks := by
  intro accepted
  exact finite_prefix_trap_rejected.2
    (LoopVCG.validity_partition_exact.mp accepted)

end APL.LoopVCG.Examples.Machine

namespace APL.LoopVCG.Examples.EntryContract

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

open VCG

private def noPre : Preconditions := fun _ => []
private def shadow : LoopAnnotations.Term :=
  .letMut (.local 1)
    (.letE
      (.whileE [.lit (.bool true)]
        (.letE (.assign 0 (.unary .not (.local 2))) (.lit (.bool false)))
        (.lit .unit))
      (.local 1))
private def originalPost : Spec := .binary .eq .result (.unary .not (.param 0))
private def reversedPost : Spec := .binary .eq .result (.unary .not (.param 1))
private def fallback : LoopVCG.ContractVC := ⟨.truth false, .truth false, ⟨[], [], 0⟩, []⟩
private def generated (post : Spec) : LoopVCG.ContractVC :=
  (generateContract #[] noPre 8 [.bool, .bool] shadow [] post).getD fallback

private theorem original_generated : generateContract #[] noPre 8 [.bool, .bool]
    shadow [] originalPost = some (generated originalPost) := by cbv

private theorem reversed_generated : generateContract #[] noPre 8 [.bool, .bool]
    shadow [] reversedPost = some (generated reversedPost) := by cbv

private theorem bool_pair (ht : params.map Val.type = [.bool, .bool]) :
    ∃ a b, params = [.bool a, .bool b] := by
  cases params with
  | nil => simp at ht
  | cons first rest =>
    cases rest with
    | nil => simp at ht
    | cons second tail =>
      cases tail with
      | cons _ _ => simp at ht
      | nil =>
        cases first <;> cases second <;> simp_all [Val.type]

private theorem original_accepted : Accepted [.bool, .bool] (generated originalPost) := by
  constructor
  · intro params _
    cbv
  constructor
  · refine ⟨[.bool true, .bool false], rfl, ?_⟩
    cbv
  · intro params typed _ extended agree
    obtain ⟨a, b, rfl⟩ := bool_pair typed
    have ha := agree 0 (by decide)
    have hb := agree 1 (by decide)
    simp [modelOf] at ha hb
    cbv
    simp [Formula.Holds, SymTerm.eval, ← ha, ← hb, embed, mUnary,
      MVal.type, mShort, mBinary]

private theorem empty_wf : LoopAnnotations.WellTyped #[] := by
  intro index fn lookup
  simp at lookup

private theorem shadow_typed : LoopAnnotations.HasType (LoopAnnotations.signatures #[])
    (LocalState.immutable [.bool, .bool].reverse) shadow .bool := by
  apply LoopAnnotations.HasType.letMut (.local rfl)
  apply LoopAnnotations.HasType.letE
  · apply LoopAnnotations.HasType.whileE (by simp)
    · intro clause member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst clause
      exact .lit
    · exact .letE (.assign rfl (.unary (.local rfl))) .lit
    · exact .lit
  · exact .local rfl

private theorem frozen_entry_post_survives_mutable_shadow :
    Accepted [.bool, .bool] (generated originalPost) ∧
    LocalState.run (LoopAnnotations.eraseFunctions #[]) 60
      (.eval shadow.erase [.bool false, .bool true] []) =
        some (.ret (.bool false) [.bool false, .bool true] []) ∧
    originalPost.eval [.bool true, .bool false] (some (.bool false)) = some (.bool true) := by
  have actual : LocalState.run (LoopAnnotations.eraseFunctions #[]) 60
      (.eval shadow.erase [.bool false, .bool true] []) =
        some (.ret (.bool false) [.bool false, .bool true] []) := by
    cbv
  refine ⟨original_accepted, actual, ?_⟩
  have post := contract_steps_value (params := [.bool true, .bool false])
    original_generated original_accepted empty_wf shadow_typed rfl (by trivial)
    (LocalState.run_sound actual).1
  exact post.2

private theorem reversed_entry_post_is_rejected : ¬ Accepted [.bool, .bool] (generated reversedPost) := by
  intro accepted
  have actual := frozen_entry_post_survives_mutable_shadow.2.1
  have post := contract_steps_value (params := [.bool true, .bool false])
    reversed_generated accepted empty_wf shadow_typed rfl (by trivial)
    (LocalState.run_sound actual).1
  simp [reversedPost, Spec.eval, embed, mShort, mUnary, mBinary, MVal.type] at post

end APL.LoopVCG.Examples.EntryContract
