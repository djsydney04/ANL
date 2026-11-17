import APL.Semantics

namespace APL.Smoke

def low : Val := .int ⟨minI64, by decide⟩
def high : Val := .int ⟨maxI64, by decide⟩
def num (n : Int) (h : InRange n := by decide) : Val := .int ⟨n, h⟩
def observe : Option State → Option Result
  | some (.ret v []) => some (.value v)
  | some (.trap t) => some (.trap t)
  | some .invalid => some .invalid
  | _ => none

example : unary .neg low = .trap .arithmeticOverflow := by decide
example : binary .add high (num 1) = .trap .arithmeticOverflow := by decide
example : binary .div low (num (-1)) = .trap .arithmeticOverflow := by decide
example : binary .rem low (num (-1)) = .trap .arithmeticOverflow := by decide
example : binary .div (num 7) (num 0) = .trap .divisionByZero := by decide
example : binary .div (num (-7)) (num 3) = .value (num (-2)) := by decide
example : binary .rem (num (-7)) (num 3) = .value (num (-1)) := by decide
example : binary .eq .unit .unit = .value (.bool true) := by decide
example : infer [] (.binary .add (.lit (.bool true)) (.lit (num 1))) = none := by decide
example : infer [] (.local 0) = none := by decide
example : infer [] (.binary .eq (.lit .unit) (.lit (.bool true))) = none := by decide
example : observe (run 20 (.eval
    (.binary .and (.lit (.bool false))
      (.binary .eq (.binary .div (.lit (num 1)) (.lit (num 0))) (.lit (num 0)))) [] [])) =
    some (.value (.bool false)) := by decide
example : observe (run 20 (.eval
    (.binary .add (.binary .div (.lit (num 1)) (.lit (num 0)))
      (.binary .add (.lit high) (.lit (num 1)))) [] [])) =
    some (.trap .divisionByZero) := by decide
example : observe (run 20 (.eval
    (.letE (.lit (num 42)) (.letE (.lit .unit) (.local 1))) [] [])) =
    some (.value (num 42)) := by decide
example : run 0 (.eval (.lit .unit) [] []) = none := rfl

end APL.Smoke
