import ANL.BootV3CheckProofs
import ANL.BootV2Carrier

namespace ANL.Boot.V3

open ANL.Words

variable {p : Program} {d : Declaration}

private theorem declaration_name_valid (h : DeclarationValid p d) : ValidName d.name := by
  cases d with
  | defined _ => exact h.name.1
  | primitive _ => exact h.identifier

private theorem declaration_not_synthetic_name (h : DeclarationValid p d) :
    d.name ≠ "__carrier_entry" := by
  cases d with
  | defined d =>
    intro eq
    have absent := h.name.2.2
    change d.function.name = "__carrier_entry" at eq
    rw [eq] at absent
    exact absent (by decide +kernel)
  | primitive d =>
    intro eq
    change d.name = "__carrier_entry" at eq
    have chars := congrArg String.toList (h.name.symm.trans eq)
    simp [String.toList_append] at chars

private theorem declaration_carrier_function (h : DeclarationValid p d) :
    d.carrierFunction.WellFormed p.carrier.signatures := by
  refine ⟨by simpa using declaration_name_valid h, ?_, ?_⟩
  · cases d with
    | defined d =>
      have empty := (V2.FunctionPolicy.memoryFree h.policy).no_sites
      change d.function.body.CanonicalSites
      simp [Term.CanonicalSites, empty]
    | primitive d =>
      simp [V2.Declaration.carrierFunction, Term.CanonicalSites, V2.dummy_no_sites]
  · cases d with
    | defined d =>
      have typed := V2.carrier_typing h.typed
      simpa [V2.Declaration.carrierFunction, Function.resourceContext, h.view,
        ANL.Memory.viewContext] using typed
    | primitive d =>
      change HasType p.carrier.signatures _ _ d.operation.dummy d.result
      rw [h.result]
      exact V2.dummy_typed d.operation

theorem carrier_wellFormed (wf : WellFormedProgram p) :
    ANL.Words.WellFormedProgram p.carrier := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change V2.carrierProfile.Admissible
    decide +kernel
  · simp only [V2.Program.carrier, Array.toList_push, List.map_append,
      List.map_map, Function.comp_def, List.map_cons, List.map_nil, V2.carrierFunction_id,
      V2.syntheticEntry, ANL.Boot.syntheticEntry,
      Array.size_push, List.size_toArray, List.length_map]
    rw [wf.ids, List.range_succ]
  · simp only [V2.Program.carrier, Array.toList_push, List.map_append,
      List.map_map, Function.comp_def, List.map_cons, List.map_nil,
      V2.carrierFunction_name, V2.syntheticEntry]
    apply List.nodup_append.mpr
    refine ⟨wf.names, by simp, ?_⟩
    intro name mem other otherMem same
    simp only [List.mem_singleton] at otherMem
    have named := same.trans otherMem
    obtain ⟨d, mem, eq⟩ := List.mem_map.mp mem
    exact declaration_not_synthetic_name (wf.declarations d mem) (eq.trans named)
  · intro fn mem
    simp only [V2.Program.carrier, Array.toList_push, List.mem_append,
      List.mem_map, List.mem_singleton] at mem
    rcases mem with ⟨d, mem, rfl⟩ | rfl
    · exact declaration_carrier_function (wf.declarations d mem)
    · exact ANL.Boot.synthetic_wellFormed
  · refine ⟨V2.syntheticEntry p.functions.length, ?_, rfl, rfl, rfl⟩
    simp [V2.Program.carrier, List.length_map]

end ANL.Boot.V3
