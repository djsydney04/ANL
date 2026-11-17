import APL.LocalStateEmbedding

namespace APL.LocalState.Examples

private def num (n : Int) (h : InRange n := by decide) : Term := .lit (.int ⟨n, h⟩)
private def value (n : Int) (h : InRange n := by decide) : Result := .value (.int ⟨n, h⟩)
private def observe : Option State → Option (Result × Env)
  | some (.ret v env []) => some (.value v, env)
  | some (.trap t) => some (.trap t, [])
  | some .invalid => some (.invalid, [])
  | _ => none

private def outerMutation : Term :=
  .letMut (num 1) (.letE (.assign 0 (num 3)) (.local 1))

example : infer #[] [] outerMutation = some .i64 := by simp [outerMutation, num, infer, Val.type]
example : observe (run #[] 30 (.eval outerMutation [] [])) = some (value 3, []) := by decide

private def conditionEffects : Term :=
  .letMut (num 0) (.letE
    (.whileE
      (.letE (.assign 0 (.binary .add (.local 0) (num 1))) (.binary .lt (.local 1) (num 4)))
      (.lit .unit))
    (.local 1))

example : infer #[] [] conditionEffects = some .i64 := by simp [conditionEffects, num, infer, Val.type, binaryType]
example : observe (run #[] 150 (.eval conditionEffects [] [])) = some (value 4, []) := by decide

private def orderedFunctions : Functions := #[
  { name := "pack", params := [.i64, .i64, .i64], result := .i64,
    body := .binary .add (.binary .add (.binary .mul (.local 2) (num 100))
      (.binary .mul (.local 1) (num 10))) (.local 0) },
  { name := "isolated", params := [.i64], result := .i64,
    body := .letMut (.local 0) (.letE (.assign 0 (num 99)) (.local 1)) }
]

private def bump : Term :=
  .letE (.assign 0 (.binary .add (.local 0) (num 1))) (.local 1)
private def triple : Term :=
  .letE (.assign 0 (.binary .mul (.local 0) (num 3))) (.local 1)
private def orderedArguments : Term :=
  .letMut (num 1) (.letE (.call 0 [bump, triple, bump])
    (.binary .add (.binary .mul (.local 0) (num 10)) (.local 1)))

example : infer (signatures orderedFunctions) [] orderedArguments = some .i64 := by
  simp [orderedArguments, orderedFunctions, bump, triple, signatures, num, infer, Val.type, binaryType]
example : observe (run orderedFunctions 150 (.eval orderedArguments [] [])) = some (value 2677, []) := by decide
example : observe (run orderedFunctions 80 (.eval
    (.letMut (num 7) (.letE (.call 1 [.local 0]) (.local 1))) [] [])) = some (value 7, []) := by decide

private def recursiveFunctions : Functions := #[
  { name := "count", params := [.i64], result := .i64,
    body := .letMut (.local 0) (.ifE (.binary .eq (.local 0) (num 0)) (num 0)
      (.letE (.assign 0 (.binary .sub (.local 0) (num 1)))
        (.binary .add (.call 0 [.local 1]) (num 1)))) }
]

example : WellTyped recursiveFunctions := by
  apply checked_functions
  intro f fn hf
  cases f with
  | zero => simp [recursiveFunctions] at hf; subst fn; simp [recursiveFunctions, signatures, immutable, num, infer, Val.type, binaryType]
  | succ f => simp [recursiveFunctions] at hf
example : observe (run recursiveFunctions 300 (.eval (.call 0 [num 5]) [] [])) = some (value 5, []) := by decide

example : infer #[] [] (.letE (num 0) (.assign 0 (num 1))) = none := by simp [infer, num, Val.type]
example : infer #[] (immutable [.i64]) (.assign 0 (num 1)) = none := by simp [infer, num, immutable, Val.type]
example : infer #[] [] (.letMut (num 0) (.letE (num 0) (.assign 0 (num 1)))) = none := by simp [infer, num, Val.type]
example : infer #[] [] (.assign 0 (num 1)) = none := by simp [infer, num, Val.type]
example : infer #[] [] (.letMut (num 0) (.assign 0 (.lit (.bool true)))) = none := by simp [infer, num, Val.type]
example : infer #[] [] (.whileE (num 0) (.lit .unit)) = none := by simp [infer, num, Val.type]
example : infer #[] [] (.whileE (.lit (.bool false)) (num 0)) = none := by simp [infer, num, Val.type]

example : observe (run #[] 3 (.eval (.whileE (.lit (.bool false)) (.lit .unit)) [] [])) =
    some (.value .unit, []) := by decide
example : observe (run #[] 2 (.eval (.whileE (.lit (.bool false)) (.lit .unit)) [] [])) = none := by decide
example : observe (run #[] 200 (.eval (.whileE (.lit (.bool true)) (.lit .unit)) [] [])) = none := by decide

example : observe (run #[] 50 (.eval (.letMut (num 0)
    (.binary .and (.lit (.bool false))
      (.letE (.assign 0 (num 1)) (.binary .eq (.binary .div (num 1) (num 0)) (num 0))))) [] [])) =
    some (.value (.bool false), []) := by decide
example : observe (run #[] 50 (.eval (.whileE (.lit (.bool true))
    (.letE (.binary .div (num 1) (num 0)) (.lit .unit))) [] [])) =
    some (.trap .divisionByZero, []) := by decide

end APL.LocalState.Examples
