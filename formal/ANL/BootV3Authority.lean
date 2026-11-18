import ANL.BootV3CheckProofs
import ANL.BootV2Authority

namespace ANL.Boot.V3
open ANL.Words

variable {p : Program}

theorem WellFormedProgram.id_at {decl : Declaration} (h : WellFormedProgram p)
    (found : p.functions[f]? = some decl) : decl.id = f := by
  have bound := List.getElem?_eq_some_iff.mp found |>.1
  have ids := congrArg (fun ids => ids[f]?) h.ids
  simpa [List.getElem?_map, found, List.getElem?_range bound] using ids

theorem EffectSetValid.machine_only_boot (valid : EffectSetValid p d)
    (present : 0 ∈ d.effects) : d.function.id = p.entries.boot.function := by
  by_cases boot : d.function.id = p.entries.boot.function
  · exact boot
  · exfalso
    have withoutMachine : d.effects = [] ∨ d.effects = [1] := by
      unfold EffectSetValid at valid
      rw [ite_eq_right boot] at valid
      split at valid
      · exact valid
      · split at valid
        · exact Or.inl valid
        · exact valid
    rcases withoutMachine with empty | uart
    · simp [empty] at present
    · simp [uart] at present

/-- All syntactic calls are checked, including unused bodies and dead branches. -/
theorem WellFormedProgram.machine_call_only_boot (valid : WellFormedProgram p)
    (caller : p.functions[f]? = some (.defined d)) (called : g ∈ calls d.function.body)
    (target : p.functions[g]? = some (.primitive row))
    (machine : 0 ∈ row.operation.effects) : f = p.entries.boot.function := by
  by_cases boot : f = p.entries.boot.function
  · exact boot
  · exfalso
    have id_eq : d.function.id = f := valid.id_at caller
    have id_different : d.function.id ≠ p.entries.boot.function := by
      simpa [id_eq] using boot
    have body_valid : DefinedValid p d := valid.at caller
    have body_policy := body_valid.policy
    unfold V2.FunctionPolicy at body_policy
    rw [ite_eq_right id_different] at body_policy
    have allowed := body_policy.2 g called
    have primitive_valid : V2.PrimitiveValid p row := valid.at target
    have present := V2.TargetAllowed.required_effect allowed target primitive_valid machine
    exact id_different (body_valid.effects.machine_only_boot present)

theorem WellFormedProgram.illegal_call_only_boot (valid : WellFormedProgram p)
    (caller : p.functions[f]? = some (.defined d)) (called : g ∈ calls d.function.body)
    (target : p.functions[g]? = some (.primitive row))
    (operation : row.operation = .illegalInstruction 0) : f = p.entries.boot.function := by
  exact valid.machine_call_only_boot caller called target (by simp [operation, V2.Operation.effects])

end ANL.Boot.V3
