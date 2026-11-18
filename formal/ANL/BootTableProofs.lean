import ANL.BootCheckProofs

namespace ANL.Boot

variable {p : Program} {i : Nat}

def definedRows (ds : List Declaration) : List Defined :=
  ds.filterMap (fun d => match d with | .defined f => some f | _ => none)

def primitiveRows (ds : List Declaration) : List Primitive :=
  ds.filterMap (fun d => match d with | .primitive f => some f | _ => none)

theorem Ordered.suffix (h : Ordered true ds) : definedRows ds = [] := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    cases h with
    | primitive tail => simpa [definedRows] using ih tail

theorem Ordered.decomposition (h : Ordered phase ds) :
    ds = (definedRows ds).map Declaration.defined ++ (primitiveRows ds).map Declaration.primitive := by
  induction h with
  | nil => rfl
  | defined _ ih =>
    simp only [definedRows, primitiveRows, List.filterMap_cons, List.map_cons, List.cons_append]
    exact congrArg (Declaration.defined _ :: ·) ih
  | primitive tail ih =>
    have empty := tail.suffix
    change definedRows _ = [] at empty
    simp only [definedRows, primitiveRows, List.filterMap_cons, List.map_cons]
    change _ = (definedRows _).map Declaration.defined ++ _
    rw [empty]
    simpa [primitiveRows, empty] using ih

theorem WellFormedProgram.decomposition (h : WellFormedProgram p) :
    p.functions = p.defined.map Declaration.defined ++ p.primitives.map Declaration.primitive :=
  h.ordered.decomposition

theorem primitive_mem {d : Primitive} (mem : d ∈ p.primitives) : Declaration.primitive d ∈ p.functions := by
  simp only [Program.primitives, List.mem_filterMap] at mem
  obtain ⟨decl, mem, eq⟩ := mem
  cases decl with
  | defined _ => contradiction
  | primitive _ => cases eq; exact mem

theorem defined_mem {d : Defined} (mem : d ∈ p.defined) : Declaration.defined d ∈ p.functions := by
  simp only [Program.defined, List.mem_filterMap] at mem
  obtain ⟨decl, mem, eq⟩ := mem
  cases decl with
  | defined _ => cases eq; exact mem
  | primitive _ => contradiction

theorem WellFormedProgram.primitive_id {d : Primitive} (h : WellFormedProgram p)
    (found : p.primitives[i]? = some d) : d.id = p.defined.length + i := by
  have lookup : p.functions[p.defined.length + i]? = some (.primitive d) := by
    rw [h.decomposition, List.getElem?_append_right (by simp)]
    simp [found]
  exact h.id_at lookup

theorem WellFormedProgram.defined_id {d : Defined} (h : WellFormedProgram p)
    (found : p.defined[i]? = some d) : d.function.id = i := by
  have lookup : p.functions[i]? = some (.defined d) := by
    rw [h.decomposition, List.getElem?_append_left (by simpa using (List.getElem?_eq_some_iff.mp found).1)]
    simp [found]
  exact h.id_at lookup

def allowedOperations (hardware : Nat) : List Operation :=
  [.read8 0 5, .write8 0 0, .write8 0 1, .write8 0 2, .write8 0 3, .write8 0 4,
    .fence 0, .csrClear 0 "sstatus" 2, .csrWrite 0 "sie" 0, .installTrap 0 hardware]

theorem Operation.Valid.member (valid : op.Valid hardware) : op ∈ allowedOperations hardware := by
  cases valid with
  | write8 mem =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl <;> simp [allowedOperations]
  | _ => simp [allowedOperations]

theorem WellFormedProgram.at_most_ten_primitives (h : WellFormedProgram p) : p.primitives.length ≤ 10 := by
  have subset : p.primitives.map Primitive.operation ⊆ allowedOperations p.entries.hardware.function := by
    intro op mem
    obtain ⟨d, hd, eq⟩ := List.mem_map.mp mem
    rw [← eq]
    exact (h.declarations _ (primitive_mem hd)).operation.member
  have bound := h.primitive_keys_unique.length_le_of_subset subset
  simpa [allowedOperations] using bound

end ANL.Boot
