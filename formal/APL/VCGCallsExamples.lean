import APL.VCGCalls

namespace APL.VCG.CallExamples

private def zero : Val := .int ⟨0, by decide⟩
private def one : Val := .int ⟨1, by decide⟩
private def seven : Val := .int ⟨7, by decide⟩
private def maximum : Val := .int ⟨maxI64, by decide⟩
private def table : Program.Functions := #[
  ⟨"choose", [.bool, .i64, .unit], .i64, .ifE (.local 2) (.local 1) (.lit zero)⟩,
  ⟨"nested", [.i64], .i64, .call 0 [.lit (.bool true), .local 0, .lit .unit]⟩]
private def preconditions : Preconditions
  | 0 => [.param 0, .binary .eq (.param 2) (.lit .unit)]
  | _ => []
private def entry : Program.Term := .call 1 [.lit seven]
private def post : Spec := .binary .eq .result (.lit (.int 7))

private theorem nested_vc : ∃ formula,
    wpCalls table preconditions 8 entry [] (specPost [] post) = some formula ∧ formula.Holds model := by
  refine ⟨_, rfl, ?_⟩
  simp [Formula.Holds, SymTerm.eval, mUnary, mBinary, mShort, MVal.type, embed, seven, zero]

example : Program.eval table 8 [] entry 20 = .ok (seven, 11) := by rfl

example : ¬ Program.Steps table (.eval entry [] []) (.trap kind) := by
  obtain ⟨formula, hgen, hvalid⟩ := nested_vc (model := modelOf [])
  exact wpCalls_steps_no_trap hgen .nil hvalid

example (hs : Program.Steps table (.eval entry [] []) (.ret value [])) :
    post.eval [] (some (embed value)) = some (.bool true) := by
  obtain ⟨formula, hgen, hvalid⟩ := nested_vc (model := modelOf [])
  exact spec_post_sound (wpCalls_steps_value hgen .nil hvalid hs) .nil

private theorem accepted_entry : ∃ vc,
    generateCallsContract table preconditions 8 [] entry [] post = some vc ∧ Accepted [] vc := by
  obtain ⟨formula, hgen, hvalid⟩ := nested_vc (model := modelOf [])
  refine ⟨⟨.truth true, .truth true, formula⟩, ?_, ?_⟩
  · simp [generateCallsContract, parameterSymbols, requiresVC, hgen]
  · constructor
    · intro params ht
      rfl
    · constructor
      · exact ⟨[], rfl, rfl⟩
      · intro params ht _
        have hp : params = [] := List.map_eq_nil_iff.mp ht
        subst params
        exact hvalid

example : ∃ vc, generateCallsContract table preconditions 8 [] entry [] post = some vc ∧
    ¬ Program.Steps table (.eval entry [] []) .invalid := by
  obtain ⟨vc, hgen, ha⟩ := accepted_entry
  exact ⟨vc, hgen, calls_contract_steps_no_invalid (params := []) hgen ha rfl (by trivial)⟩

private def divideZero : Program.Term := .binary .div (.lit one) (.lit zero)
private def overflow : Program.Term := .binary .add (.lit maximum) (.lit one)
private def ignored : Program.Functions := #[⟨"ignored", [.i64, .i64], .unit, .lit .unit⟩]

example : Program.eval ignored 8 [] (.call 0 [divideZero, overflow]) 20 =
    .error (.trap .divisionByZero) := by rfl

example : Program.eval ignored 8 [] (.call 0 [overflow, divideZero]) 20 =
    .error (.trap .arithmeticOverflow) := by rfl

example (hgen : wpCalls ignored (fun _ => []) 8 (.call 0 [divideZero, overflow]) []
    (fun _ => some (.truth true)) = some formula) : ¬ formula.Holds model := by
  intro hv
  have hs := wpCalls_no_trap (depth := 8) (fuel := 20) (kind := .divisionByZero) hgen .nil hv
  exact hs rfl

example (hgen : wpCalls ignored (fun _ => []) 8 (.call 0 [overflow, divideZero]) []
    (fun _ => some (.truth true)) = some formula) : ¬ formula.Holds model := by
  intro hv
  have hs := wpCalls_no_trap (depth := 8) (fuel := 20) (kind := .arithmeticOverflow) hgen .nil hv
  exact hs rfl

private def undefined : Spec :=
  .binary .eq (.binary .div (.lit (.int 1)) (.lit (.int 0))) (.lit (.int 0))
private def unitTable : Program.Functions := #[⟨"unit", [], .unit, .lit .unit⟩]

example (hgen : invokeWP unitTable (fun _ => [.lit (.bool false), undefined])
    (wpCalls unitTable (fun _ => []) 1) 0 [] (fun _ => some (.truth true)) = some formula) :
    ¬ formula.Holds model := by
  intro hv
  have hs := invokeWP_preconditions hgen (EnvRep.nil : EnvRep model [] []) hv
  simp [RequiresHold, Spec.eval] at hs

example (hgen : invokeWP unitTable (fun _ => [undefined, .lit (.bool false)])
    (wpCalls unitTable (fun _ => []) 1) 0 [] (fun _ => some (.truth true)) = some formula) :
    ¬ formula.Holds model := by
  intro hv
  have hs := invokeWP_preconditions hgen (EnvRep.nil : EnvRep model [] []) hv
  simp [RequiresDefined, undefined, Spec.eval, mShort, mBinary] at hs

example : RequiresDefined [] [.lit (.bool false), undefined] := by
  simp [RequiresDefined, Spec.eval]

example : ¬ RequiresDefined [] [undefined, .lit (.bool false)] := by
  simp [RequiresDefined, undefined, Spec.eval, mShort, mBinary]

example : wpCalls table preconditions 8 (.call 0 [.lit (.bool true)]) []
    (fun _ => some (.truth true)) = none := by rfl

example : wpCalls table preconditions 8
    (.ifE (.lit (.bool true)) (.lit .unit) (.call 9 [])) []
    (fun _ => some (.truth true)) = none := by rfl

example : wpCalls unitTable (fun _ => [.result]) 8 (.call 0 []) []
    (fun _ => some (.truth true)) = none := by rfl

private def recursive : Program.Functions := #[⟨"recursive", [], .unit, .call 0 []⟩]

example : wpCalls recursive (fun _ => []) 8 (.call 0 []) []
    (fun _ => some (.truth true)) = none := by rfl

example : wpCalls table preconditions 0 entry [] (specPost [] post) = none := by rfl

end APL.VCG.CallExamples
