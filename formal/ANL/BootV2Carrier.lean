import ANL.BootV2CheckProofs
import ANL.BootCarrier

namespace ANL.Boot.V2

open ANL.Words

variable {p : Program} {f : Nat} {d : Declaration}

/-- Internal typing scaffolding only; never an executable boot-program export. -/
abbrev carrierProfile := ANL.Boot.carrierProfile
abbrev syntheticEntry := ANL.Boot.syntheticEntry

def Operation.dummy : Operation → Term
  | .legacy op => op.dummy
  | .illegalInstruction _ => .lit unitTy .unit

def Declaration.carrierFunction : Declaration → Function
  | .defined d => d.function
  | .primitive d => ⟨d.id, d.name, none, d.params, d.result, d.operation.dummy⟩

/-- No executable boot route may expose this ordinary-language proof adapter. -/
def Program.carrier (p : Program) : ANL.Words.Program :=
  ⟨"anl-core-v4", "anl-words-v1", carrierProfile,
    (p.functions.map Declaration.carrierFunction).toArray.push (syntheticEntry p.functions.length),
    p.functions.length⟩

@[simp] theorem carrierFunction_signature (d : Declaration) :
    d.carrierFunction.signature = d.signature := by cases d <;> rfl

@[simp] theorem carrierFunction_id (d : Declaration) : d.carrierFunction.id = d.id := by cases d <;> rfl

@[simp] theorem carrierFunction_name (d : Declaration) : d.carrierFunction.name = d.name := by cases d <;> rfl

theorem carrier_signatures : p.carrier.signatures = p.signatures.push (syntheticEntry p.functions.length).signature := by
  simp [Program.carrier, ANL.Words.Program.signatures, Program.signatures, List.map_map]

theorem carrier_lookup (found : p.signatures[f]? = some signature) :
    p.carrier.signatures[f]? = some signature := by
  rw [carrier_signatures, Array.getElem?_push_lt (Array.getElem?_eq_some_iff.mp found).1]
  exact congrArg some (Array.getElem?_eq_some_iff.mp found).2

theorem carrier_typing (h : HasType p.signatures Γ R e t) : HasType p.carrier.signatures Γ R e t :=
  ANL.Boot.typing_with_signatures h (fun _ _ => carrier_lookup)

theorem dummy_typed (op : Operation) : HasType sigs Γ R op.dummy op.result := by
  cases op with
  | legacy op => exact ANL.Boot.dummy_typed op
  | illegalInstruction authority => exact .lit (v := .unit)

theorem dummy_no_sites (op : Operation) : op.dummy.heapSites = [] := by
  cases op with
  | legacy op => exact ANL.Boot.dummy_no_sites op
  | illegalInstruction authority => simp [Operation.dummy, Term.heapSites]

theorem DeclarationValid.name_valid (h : DeclarationValid p d) : ValidName d.name := by
  cases d with
  | defined _ => exact h.name.1
  | primitive _ => exact h.identifier

theorem DeclarationValid.not_synthetic_name (h : DeclarationValid p d) : d.name ≠ "__carrier_entry" := by
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

theorem DeclarationValid.carrier_function (h : DeclarationValid p d) :
    d.carrierFunction.WellFormed p.carrier.signatures := by
  refine ⟨by simpa using h.name_valid, ?_, ?_⟩
  · cases d with
    | defined d =>
      have empty := h.policy.memoryFree.no_sites
      change d.function.body.CanonicalSites
      simp [Term.CanonicalSites, empty]
    | primitive d => simp [Declaration.carrierFunction, Term.CanonicalSites, dummy_no_sites]
  · cases d with
    | defined d =>
      have typed := carrier_typing h.typed
      simpa [Declaration.carrierFunction, Function.resourceContext, h.view, ANL.Memory.viewContext] using typed
    | primitive d =>
      change HasType p.carrier.signatures _ _ d.operation.dummy d.result
      rw [h.result]
      exact dummy_typed d.operation

theorem carrier_wellFormed (h : WellFormedProgram p) : ANL.Words.WellFormedProgram p.carrier := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change carrierProfile.Admissible; decide +kernel
  · simp only [Program.carrier, Array.toList_push, List.map_append,
      List.map_map, Function.comp_def, List.map_cons, List.map_nil, carrierFunction_id, syntheticEntry, ANL.Boot.syntheticEntry,
      Array.size_push, List.size_toArray, List.length_map]
    rw [h.ids, List.range_succ]
  · simp only [Program.carrier, Array.toList_push, List.map_append,
      List.map_map, Function.comp_def, List.map_cons, List.map_nil, carrierFunction_name, syntheticEntry]
    apply List.nodup_append.mpr
    refine ⟨h.names, by simp, ?_⟩
    intro name mem other otherMem same
    simp only [List.mem_singleton] at otherMem
    have named := same.trans otherMem
    obtain ⟨d, mem, eq⟩ := List.mem_map.mp mem
    exact (h.declarations d mem).not_synthetic_name (eq.trans named)
  · intro fn mem
    simp only [Program.carrier, Array.toList_push, List.mem_append,
      List.mem_map, List.mem_singleton] at mem
    rcases mem with ⟨d, mem, rfl⟩ | rfl
    · exact (h.declarations d mem).carrier_function
    · exact ANL.Boot.synthetic_wellFormed
  · refine ⟨syntheticEntry p.functions.length, ?_, rfl, rfl, rfl⟩
    simp [Program.carrier, List.length_map]

theorem carrier_checked (h : checkProgram p = true) : ANL.Words.checkProgram p.carrier = true :=
  ANL.Words.checkProgram_iff.mpr (carrier_wellFormed (checkProgram_iff.mp h))

end ANL.Boot.V2
