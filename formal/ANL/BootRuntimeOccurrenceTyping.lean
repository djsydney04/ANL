import ANL.BootRuntimeOrdinarySafety

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program} {ident : Nat}
set_option linter.unusedSimpArgs false

 theorem arguments_member_typed (typed : ArgsTyped sigs Γ R terms types) (member : term ∈ terms) :
    ∃ ty, HasType sigs Γ R term ty := by
  induction terms generalizing types with
  | nil => cases member
  | cons first rest ih =>
    cases typed with | cons head tail =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, head⟩
      · exact ih tail member

 theorem child_typed (child : Origin.Child term edge next) (typed : HasType sigs Γ R term ty) :
    ∃ Δ u, HasType sigs Δ R next u := by
  cases child <;> cases typed
  all_goals first
    | exact ⟨_, _, by assumption⟩
    | have element := arguments_member_typed (by assumption) (List.mem_of_getElem? (by assumption))
      obtain ⟨u, hu⟩ := element
      exact ⟨_, u, hu⟩

 theorem occurrence_typed (occurrence : Origin.At term path next) (typed : HasType sigs Γ R term ty) :
    ∃ Δ u, HasType sigs Δ R next u := by
  induction occurrence generalizing Γ ty with
  | root => exact ⟨_, _, typed⟩
  | child edge _ ih =>
    obtain ⟨Δ, u, hu⟩ := child_typed edge typed
    exact ih hu

 theorem located_typed (wf : WellFormedProgram p) (located : Origin.Located p origin term) :
    ∃ Γ ty, HasType p.signatures Γ [] term ty := by
  cases located with | intro found occurrence =>
    exact occurrence_typed occurrence (wf.declarations _ (List.mem_of_getElem? found)).typed

 theorem declaration_signature (found : p.functions[ident]? = some row) :
    p.signatures[ident]? = some row.signature := by
  simp [Program.signatures, List.getElem?_map, found]

 theorem primitive_valid (wf : WellFormedProgram p) (found : p.functions[ident]? = some (.primitive row)) :
    PrimitiveValid p row := wf.declarations _ (List.mem_of_getElem? found)

 theorem primitive_carrier_signature (found : p.functions[ident]? = some (.primitive row)) :
    p.carrier.signatures[ident]? = some ⟨none, row.params, row.result⟩ :=
  carrier_lookup (declaration_signature found)

 theorem located_call_result (wf : WellFormedProgram p)
    (located : Origin.Located p origin (.call ty ident args))
    (found : p.functions[ident]? = some (.primitive row)) : ty = row.operation.result := by
  obtain ⟨Γ, u, typed⟩ := located_typed wf located
  cases typed with
  | call signature _ _ =>
    have same := Option.some.inj (signature.symm.trans (declaration_signature found))
    cases same
    exact (primitive_valid wf found).result

 theorem typed_invoke_arguments (typed : Words.State.Typed p.carrier ⟨.invoke ident none values, a, k, w⟩ t)
    (found : p.functions[ident]? = some (.primitive row)) : values.reverse.map Val.type = row.params := by
  cases typed with | intro env control frames layout world =>
   cases control with | invoke signature _ params _ =>
    have same := Option.some.inj (signature.symm.trans (primitive_carrier_signature found))
    cases same
    simpa [List.map_reverse] using params.symm

 theorem invoke_return_typed (typed : Words.State.Typed p.carrier ⟨.invoke ident none values, a, k, w⟩ t)
    (found : p.functions[ident]? = some (.primitive row)) (result : value.type = row.result) :
    Words.State.Typed p.carrier ⟨.ret value, a, k, w⟩ t := by
  cases typed with | intro env control frames layout world =>
   cases control with | invoke signature _ _ _ =>
    have same := Option.some.inj (signature.symm.trans (primitive_carrier_signature found))
    cases same
    exact Words.typed_ret env (result ▸ frames) layout world

end ANL.Boot.Runtime
