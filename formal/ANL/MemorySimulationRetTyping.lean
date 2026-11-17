import ANL.MemorySimulationMatch

namespace ANL.Memory.Simulation

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

theorem logical_boolean (logical : op = .and ∨ op = .or)
    (valid : APL.FlatProducts.binaryType op value.type rightType = some resultType) :
    ∃ b, value = APL.FlatProducts.Val.scalar (.bool b) := by
  cases value with
  | scalar v =>
      cases v with
      | bool b => exact ⟨b, rfl⟩
      | int n =>
          rcases logical with rfl | rfl <;> cases rightType with
          | scalar scalar => cases scalar <;> simp [APL.FlatProducts.binaryType, APL.FlatProducts.Val.type, APL.Val.type, APL.binaryType] at valid
          | tuple shape => simp [APL.FlatProducts.binaryType, APL.FlatProducts.Val.type] at valid
      | unit =>
          rcases logical with rfl | rfl <;> cases rightType with
          | scalar scalar => cases scalar <;> simp [APL.FlatProducts.binaryType, APL.FlatProducts.Val.type, APL.Val.type, APL.binaryType] at valid
          | tuple shape => simp [APL.FlatProducts.binaryType, APL.FlatProducts.Val.type] at valid
  | tuple values =>
      rcases logical with rfl | rfl <;> cases rightType <;>
        simp [APL.FlatProducts.binaryType, APL.FlatProducts.Val.type] at valid

theorem typed_logical_left (logical : op = .and ∨ op = .or)
    (typed : State.Typed p ⟨.ret value, a, .left op right :: k, w⟩ ty) :
    ∃ b, value = APL.FlatProducts.Val.scalar (.bool b) := by
  obtain ⟨_, _, _, _, _, frame⟩ := typed_ret_frame typed
  cases frame with
  | left _ valid => exact logical_boolean logical valid

theorem nonlogical_not_short (notAnd : op ≠ .and) (notOr : op ≠ .or) (value : Val) :
    APL.FlatProducts.shortCircuit op value = false := by
  cases op <;> cases value <;> simp_all [APL.FlatProducts.shortCircuit, APL.shortCircuit]

end ANL.Memory.Simulation
