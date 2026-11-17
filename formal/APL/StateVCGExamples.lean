import APL.StateVCGContracts

namespace APL.StateVCG.Examples
open VCG

private def num (n : Int) (h : InRange n := by decide) : LocalState.Term := .lit (.int ⟨n, h⟩)
private def value (n : Int) (h : InRange n := by decide) : Val := .int ⟨n, h⟩
private def expect (n : Int) : StatePost := fun result _ =>
  some (.holds (.binary .eq result (.lit (.int n))))
private def confirms (fs : LocalState.Functions) (e : LocalState.Term) (n : Int) : Prop :=
  ∃ formula, wp fs (fun _ => []) 20 e [] (expect n) = some formula ∧ formula.Holds (modelOf [])

private def rhsState : LocalState.Term :=
  .letMut (num 1) (.letE
    (.assign 0 (.letE (.assign 0 (num 2)) (num 3))) (.local 1))
private def outerState : LocalState.Term :=
  .letMut (num 1) (.letE (.letE (num 9) (.assign 1 (num 2))) (.local 1))
private def shadowState : LocalState.Term :=
  .letMut (num 1) (.letE (.letMut (num 2) (.assign 0 (num 3))) (.local 1))
private def initializerState : LocalState.Term :=
  .letMut (num 1) (.letE (.letE (.assign 0 (num 2)) (num 3))
    (.binary .add (.binary .mul (.local 0) (num 10)) (.local 1)))

example : confirms #[] rhsState 3 := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, mBinary, mShort, MVal.type, VCG.embed]
example : confirms #[] outerState 2 := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, mBinary, mShort, MVal.type, VCG.embed]
example : confirms #[] shadowState 1 := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, mBinary, mShort, MVal.type, VCG.embed]
example : confirms #[] initializerState 32 := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, binaryGuard, mBinary, mShort, MVal.type, VCG.embed, InRange, minI64, maxI64]
example : LocalState.run #[] 60 (.eval rhsState [] []) = some (.ret (value 3) [] []) := by rfl
example : LocalState.run #[] 60 (.eval outerState [] []) = some (.ret (value 2) [] []) := by rfl

example : ∃ formula, wp #[] (fun _ => []) 8
    (.letE (num 9) (.assign 1 (num 2))) [.lit (.int 1)]
    (fun _ env => env[0]?.map (fun symbol => .holds (.binary .eq symbol (.lit (.int 2))))) =
    some formula ∧ formula.Holds (modelOf []) := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, mBinary, mShort, MVal.type, VCG.embed]
example : LocalState.run #[] 30 (.eval (.letE (num 9) (.assign 1 (num 2))) [value 1] []) =
    some (.ret .unit [value 2] []) := by rfl

private def bump : LocalState.Term :=
  .letE (.assign 0 (.binary .add (.local 0) (num 1))) (.local 1)
private def triple : LocalState.Term :=
  .letE (.assign 0 (.binary .mul (.local 0) (num 3))) (.local 1)
private def binaryState : LocalState.Term := .letMut (num 0) (.binary .add bump bump)
private def branchState (test : Bool) : LocalState.Term :=
  .letMut (num 0) (.ifE (.letE (.assign 0 (num 2)) (.lit (.bool test))) bump triple)
private def shortState : LocalState.Term :=
  .letMut (num 0) (.letE (.binary .and
    (.letE (.assign 0 (num 2)) (.lit (.bool false)))
    (.letE (.assign 0 (num 9)) (.binary .eq (.binary .div (num 1) (num 0)) (num 0))))
    (.local 1))

example : confirms #[] binaryState 3 := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, binaryGuard, mBinary, mShort, MVal.type, VCG.embed, InRange, minI64, maxI64]
example : confirms #[] (branchState true) 3 := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, binaryGuard, mUnary, mBinary, mShort, MVal.type, VCG.embed, InRange, minI64, maxI64]
example : confirms #[] (branchState false) 6 := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, binaryGuard, mUnary, mBinary, mShort, MVal.type, VCG.embed, InRange, minI64, maxI64]
example : confirms #[] shortState 2 := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, shortGuard, mUnary, mBinary, mShort, MVal.type, VCG.embed]

private def functions : LocalState.Functions := #[
  { name := "pack", params := [.i64, .i64, .i64], result := .i64,
    body := .binary .add (.binary .add (.binary .mul (.local 2) (num 100))
      (.binary .mul (.local 1) (num 10))) (.local 0) },
  { name := "isolated", params := [.i64], result := .i64,
    body := .letMut (.local 0) (.letE (.assign 0 (num 99)) (.local 1)) },
  { name := "choose", params := [.bool, .i64, .unit], result := .i64,
    body := .ifE (.local 2) (.local 1) (num 0) }
]
private def orderedArguments : LocalState.Term :=
  .letMut (num 1) (.letE (.call 0 [bump, triple, bump])
    (.binary .add (.binary .mul (.local 0) (num 10)) (.local 1)))
private def isolatedCall : LocalState.Term :=
  .letMut (num 1) (.letE (.call 1 [bump])
    (.binary .add (.binary .mul (.local 0) (num 10)) (.local 1)))

private theorem ordered_vc : confirms functions orderedArguments 2677 := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, binaryGuard, mBinary, mShort, MVal.type, VCG.embed, InRange, minI64, maxI64]
private def capturedPreconditions : Preconditions
  | 0 => [.binary .eq (.param 0) (.lit (.int 2)),
      .binary .eq (.param 1) (.lit (.int 6)), .binary .eq (.param 2) (.lit (.int 7))]
  | _ => []
example : ∃ formula, wp functions capturedPreconditions 20 orderedArguments [] (expect 2677) =
    some formula ∧ formula.Holds (modelOf []) := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, binaryGuard, mBinary, mShort, MVal.type, VCG.embed, InRange, minI64, maxI64]
example : confirms functions isolatedCall 992 := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, binaryGuard, mBinary, mShort, MVal.type, VCG.embed, InRange, minI64, maxI64]
example : confirms functions (.call 2 [.lit (.bool true), num 7, .lit .unit]) 7 := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, mUnary, mBinary, mShort, MVal.type, VCG.embed]
example : LocalState.run functions 180 (.eval orderedArguments [] []) =
    some (.ret (value 2677) [] []) := by rfl
example : LocalState.run functions 100 (.eval isolatedCall [] []) =
    some (.ret (value 992) [] []) := by rfl

example : ¬ LocalState.Steps functions (.eval orderedArguments [] []) (.trap kind) := by
  obtain ⟨formula, hgen, hvalid⟩ := ordered_vc
  exact wp_steps_no_trap hgen .nil hvalid
example (trace : LocalState.Steps functions (.eval orderedArguments [] []) (.ret result env [])) :
    StatePostHolds (modelOf []) (expect 2677) result env := by
  obtain ⟨formula, hgen, hvalid⟩ := ordered_vc
  exact wp_steps_value hgen .nil hvalid trace

private def increment : LocalState.Term := .letMut (.local 0)
  (.letE (.assign 0 (.binary .add (.local 0) (num 1))) (.local 1))
private def incReq : Spec := .binary .lt (.param 0) (.lit (.int maxI64))
private def incPost : Spec := .binary .eq .result (.binary .add (.param 0) (.lit (.int 1)))
private def incVC : ContractVC := {
  requiresDefined := .and (.boolean (.binary .lt (.var 0) (.lit (.int maxI64))))
    (.imp (.holds (.binary .lt (.var 0) (.lit (.int maxI64)))) (.truth true)),
  requiresTruth := .and (.holds (.binary .lt (.var 0) (.lit (.int maxI64)))) (.truth true),
  body := .and (.range (.binary .add (.var 0) (.lit (.int 1))))
    (.holds (.binary .eq (.binary .add (.var 0) (.lit (.int 1))) (.binary .add (.var 0) (.lit (.int 1))))) }

private theorem increment_generated : generateContract #[] (fun _ => []) 8 [.i64]
    increment [incReq] incPost = some incVC := by rfl
private theorem integer_parameter (h : params.map Val.type = [.i64]) : ∃ n, params = [.int n] := by
  cases params with
  | nil => contradiction
  | cons v rest =>
    cases rest with
    | cons _ _ => simp at h
    | nil => cases v with
      | int n => exact ⟨n, rfl⟩
      | bool _ | unit => simp [Val.type] at h

private theorem increment_accepted : Accepted [.i64] incVC := by
  constructor
  · intro params ht
    obtain ⟨n, rfl⟩ := integer_parameter ht
    simp [incVC, Formula.Holds, SymTerm.eval, modelOf, mShort, mBinary, VCG.embed]
  · constructor
    · exact ⟨[value 0], rfl, by simp [incVC, Formula.Holds, SymTerm.eval, modelOf, mShort, mBinary, VCG.embed, value, maxI64]⟩
    · intro params ht hpre
      obtain ⟨n, rfl⟩ := integer_parameter ht
      simp [incVC, Formula.Holds, SymTerm.eval, modelOf, mShort, mBinary, VCG.embed] at hpre ⊢
      have hn := n.property
      unfold InRange at hn ⊢
      omega

example {params : Env} (ht : params.map Val.type = [.i64])
    (hpre : RequiresHold (params.map VCG.embed) [incReq]) :
    RunSafe (fun result _ => result.type = .i64 ∧
      incPost.eval (params.map VCG.embed) (some (VCG.embed result)) = some (.bool true))
      (LocalState.run #[] fuel (.eval increment params.reverse [])) := by
  apply contract_run_sound increment_generated increment_accepted
  · intro f fn hf; simp at hf
  · apply LocalState.infer_sound
    simp [LocalState.infer, LocalState.signatures, LocalState.immutable, increment, num, Val.type, binaryType]
  · exact ht
  · exact hpre

private def overflow : LocalState.Term := .binary .add (num maxI64) (num 1)
private def discardedOverflow : LocalState.Term :=
  .letMut (num 0) (.letE (.assign 0 overflow) (num 0))
example (hwp : wp #[] (fun _ => []) 8 discardedOverflow [] (expect 0) = some formula) :
    ¬ formula.Holds (modelOf []) := by
  intro hf
  have safe := wp_run_sound (fuel := 50) hwp .nil hf
  have hr : LocalState.run #[] 50 (.eval discardedOverflow [] []) = some (.trap .arithmeticOverflow) := by rfl
  simp only [hr, RunSafe] at safe

example (hgen : generateContract #[] (fun _ => []) 8 [] (num 0)
    [.lit (.bool false)] (.lit (.bool true)) = some vc) : ¬ Accepted [] vc := by
  intro ha
  obtain ⟨params, _, hpre⟩ := contract_nonvacuous hgen ha
  simp [RequiresHold, Spec.eval] at hpre

private def undefined : Spec :=
  .binary .eq (.binary .div (.lit (.int 1)) (.lit (.int 0))) (.lit (.int 0))
private def unitFunctions : LocalState.Functions := #[⟨"unit", [], .unit, .lit .unit⟩]
example (hgen : invokeWP unitFunctions (fun _ => [undefined])
    (wp unitFunctions (fun _ => []) 1) 0 [] [] (fun _ _ => some (.truth true)) = some formula) :
    ¬ formula.Holds model := by
  intro hf
  have h := invoke_preconditions hgen (EnvRep.nil : EnvRep model [] []) hf
  simp [RequiresDefined, undefined, Spec.eval, mShort, mBinary] at h
example (hgen : invokeWP unitFunctions (fun _ => [.lit (.bool false)])
    (wp unitFunctions (fun _ => []) 1) 0 [] [] (fun _ _ => some (.truth true)) = some formula) :
    ¬ formula.Holds model := by
  intro hf
  have h := invoke_preconditions hgen (EnvRep.nil : EnvRep model [] []) hf
  simp [RequiresHold, Spec.eval] at h

example : wp #[] (fun _ => []) 8 (.assign 0 (num 1)) [] (expect 1) = none := by rfl
example : wp functions (fun _ => []) 8 (.call 2 [num 1]) [] (expect 1) = none := by rfl
example : wp #[] (fun _ => []) 8
    (.ifE (.lit (.bool true)) (num 1) (.call 9 [])) [] (expect 1) = none := by rfl
example : wp #[] (fun _ => []) 8
    (.ifE (.lit (.bool true)) (num 1)
      (.letE (.whileE (.lit (.bool false)) (.lit .unit)) (num 1))) []
    (expect 1) = none := by rfl
example : wp #[] (fun _ => []) 8
    (.binary .and (.lit (.bool false))
      (.letE (.whileE (.lit (.bool false)) (.lit .unit)) (.lit (.bool true)))) []
    (fun _ _ => some (.truth true)) = none := by rfl
private def recursive : LocalState.Functions := #[⟨"recursive", [], .unit, .call 0 []⟩]
example : wp recursive (fun _ => []) 8 (.call 0 []) [] (fun _ _ => some (.truth true)) = none := by rfl
example : wp #[] (fun _ => []) 0 (num 1) [] (expect 1) = none := by rfl

-- Operational generation does not check static permissions. Typed wrappers do.
example : LocalState.infer #[] (LocalState.immutable [.i64]) (.assign 0 (num 1)) = none := by simp [LocalState.infer, LocalState.immutable, num, Val.type]
example : wp #[] (fun _ => []) 8 (.assign 0 (num 1)) [.lit (.int 0)]
    (fun _ _ => some (.truth true)) = some (.truth true) := by rfl

end APL.StateVCG.Examples
