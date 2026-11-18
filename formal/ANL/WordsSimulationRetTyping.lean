import ANL.WordsSimulationMatch

namespace ANL.Words.Simulation

open ANL.Memory

theorem typed_ret_frame (typed : State.Typed p ⟨.ret value, a, frame :: k, w⟩ ty) :
    ∃ Γ Δ resources fn result, Frame.Typed p.signatures frame Γ a.resources a.function value.type Δ resources fn result := by
  rcases typed with ⟨env, control, kont, layout, world⟩
  dsimp only at control kont
  cases control
  cases kont with
  | cons head tail => exact ⟨_, _, _, _, _, head⟩

theorem typed_writeIndex_permission
    (typed : State.Typed p ⟨.ret value, a, .writeIndex resource body :: k, w⟩ ty) : resource.mode.CanWrite := by
  obtain ⟨_, _, _, _, _, frame⟩ := typed_ret_frame typed
  generalize value.type = input at frame
  cases frame with
  | writeIndex _ permission _ => exact permission

theorem typed_view_permission
    (typed : State.Typed p ⟨.ret value, a, .arguments functionId (some sourceLoan) remaining prior :: k, w⟩ ty) :
    sourceLoan.source.mode.CanLend sourceLoan.mode := by
  obtain ⟨_, _, _, _, _, frame⟩ := typed_ret_frame typed
  cases frame with
  | arguments _ _ _ _ valid => exact valid.2

theorem typed_heapLength_function
    (typed : State.Typed p ⟨.ret value, a, .heapLength site initializer yes no :: k, w⟩ ty) :
    site.function = a.function := by
  obtain ⟨_, _, _, _, _, frame⟩ := typed_ret_frame typed
  generalize value.type = input at frame
  cases frame with
  | heapLength same _ _ _ => exact same

private theorem logical_input_type (h : BinarySig op u v t)
    (hop : op = .legacy .and ∨ op = .legacy .or) :
    u = .scalar (.legacy .bool) ∧ v = .scalar (.legacy .bool) ∧ t = .scalar (.legacy .bool) := by
  rcases hop with rfl | rfl <;> cases h <;> simp_all [WordArithmeticOp, WordCompareOp]
  all_goals rename_i a b result hop
  all_goals cases a <;> cases b <;> simp_all [APL.binaryType]

theorem logical_boolean (logical : op = (.legacy .and) ∨ op = (.legacy .or))
    (valid : BinarySig op value.type rightType resultType) :
    ∃ b, value = ANL.Words.Val.scalar (.legacy (.bool b)) := by
  have typed := (logical_input_type valid logical).1
  cases value with
  | scalar v =>
      cases v with
      | legacy v =>
          cases v with
          | bool b => exact ⟨b, rfl⟩
          | int n => simp [Val.type, ScalarVal.type, APL.Val.type] at typed
          | unit => simp [Val.type, ScalarVal.type, APL.Val.type] at typed
      | word v => simp [Val.type, ScalarVal.type] at typed
  | tuple values => simp [Val.type] at typed

theorem typed_logical_left (logical : op = (.legacy .and) ∨ op = (.legacy .or))
    (typed : State.Typed p ⟨.ret value, a, .left op right :: k, w⟩ ty) :
    ∃ b, value = ANL.Words.Val.scalar (.legacy (.bool b)) := by
  obtain ⟨_, _, _, _, _, frame⟩ := typed_ret_frame typed
  cases frame with
  | left _ valid => exact logical_boolean logical valid

theorem nonlogical_not_short (notAnd : op ≠ (.legacy .and)) (notOr : op ≠ (.legacy .or)) (value : Val) :
    ANL.Words.shortCircuit op value = false := by
  cases value with
  | tuple fields => rfl
  | scalar value =>
      cases value with
      | word word => rfl
      | legacy value =>
          cases op <;> simp_all [ANL.Words.shortCircuit, APL.shortCircuit]

end ANL.Words.Simulation
