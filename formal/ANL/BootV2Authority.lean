import ANL.BootV2CheckProofs

namespace ANL.Boot.V2
open ANL.Words

theorem EffectSetValid.machine_only_boot (valid : EffectSetValid p d)
    (present : 0 ∈ d.effects) : d.function.id = p.entries.boot.function := by
  by_cases different : d.function.id = p.entries.boot.function
  · exact different
  · exfalso
    unfold EffectSetValid at valid
    rw [ite_eq_right different] at valid
    split at valid
    · simp [valid] at present
    · rcases valid with empty | uart
      · simp [empty] at present
      · simp [uart] at present

theorem TargetAllowed.required_effect (allowed : TargetAllowed p effects f)
    (found : p.functions[f]? = some (.primitive row))
    (valid : PrimitiveValid p row) (member : effect ∈ row.operation.effects) :
    effect ∈ effects := by
  have requirements := allowed.2
  simp only [found] at requirements
  exact requirements.2 effect (by simpa [valid.effects] using member)

/-- Includes dead and unused function bodies; this is not a reachability claim. -/
theorem WellFormedProgram.illegal_call_only_boot (valid : WellFormedProgram p)
    (caller : p.functions[f]? = some (.defined d)) (called : g ∈ calls d.function.body)
    (target : p.functions[g]? = some (.primitive row))
    (operation : row.operation = .illegalInstruction 0) : f = p.entries.boot.function := by
  by_cases different : f = p.entries.boot.function
  · exact different
  · exfalso
    have id_eq : d.function.id = f := valid.id_at caller
    have id_different : d.function.id ≠ p.entries.boot.function := by
      simpa [id_eq] using different
    have body_valid : DefinedValid p d := valid.at caller
    have body_policy := body_valid.policy
    unfold FunctionPolicy at body_policy
    rw [ite_eq_right id_different] at body_policy
    have allowed := body_policy.2 g called
    have primitive_valid : PrimitiveValid p row := valid.at target
    have zero : 0 ∈ row.operation.effects := by simp [operation, Operation.effects]
    have present := allowed.required_effect target primitive_valid zero
    exact id_different (body_valid.effects.machine_only_boot present)

theorem PrimitiveValid.illegal_signature (valid : PrimitiveValid p row)
    (operation : row.operation = .illegalInstruction 0) :
    row.params = [] ∧ row.result = unitTy ∧ row.effects = [0] := by
  simpa [operation, Operation.params, Operation.result, Operation.effects]
    using And.intro valid.params (And.intro valid.result valid.effects)

end ANL.Boot.V2
