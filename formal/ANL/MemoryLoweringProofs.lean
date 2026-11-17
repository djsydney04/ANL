import ANL.MemoryLoweringTyping
import ANL.MemoryLoweringInventory

namespace ANL.Memory.Lowering

private theorem functions_length {fs : List Function} {outs : List Mir.Function}
    (h : fs.mapM function = some outs) : outs.length = fs.length := by
  induction fs generalizing outs with
  | nil => simpa using h.symm
  | cons fn rest ih =>
      simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at h
      obtain ⟨out, _, tail, ht, eq⟩ := h
      cases eq
      simp [ih ht]

private theorem functions_lookup {fs : List Function} {outs : List Mir.Function}
    (h : fs.mapM function = some outs) (i : Nat) :
    outs[i]? = (fs[i]?).bind function := by
  induction fs generalizing outs i with
  | nil => cases h; rfl
  | cons fn rest ih =>
      simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at h
      obtain ⟨out, hf, tail, ht, eq⟩ := h
      cases eq
      cases i with
      | zero => simpa using hf.symm
      | succ i => exact ih ht i

private theorem functions_signatures {fs : List Function} {outs : List Mir.Function}
    (h : fs.mapM function = some outs) :
    outs.map Mir.Function.signature = fs.map Function.signature := by
  induction fs generalizing outs with
  | nil => cases h; rfl
  | cons fn rest ih =>
      simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at h
      obtain ⟨out, hf, tail, ht, eq⟩ := h
      cases eq
      simp only [List.map_cons, (function_metadata hf).2.1, ih ht]

theorem function_wellFormed {fn : Function} {out : Mir.Function}
    (h : fn.WellFormed sigs) (lowered : function fn = some out) : out.WellFormed sigs := by
  obtain ⟨ht, hs, hr⟩ := function_tables h.sites lowered
  exact ⟨ht, hs, hr, function_typed h.body lowered⟩

theorem program_metadata {p : Program} {out : Mir.Program} (lowered : program p = some out) :
    out.schema = "anl-memory-mir-v1" ∧ out.semanticRevision = p.semanticRevision ∧
    out.allocationProfile = p.profile ∧ out.entry = p.entry ∧
    out.functions.size = p.functions.size ∧ out.signatures = p.signatures ∧
    ∀ i : Nat, out.functions[i]? = (p.functions[i]?).bind function := by
  simp only [program, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨fs, hf, eq⟩ := lowered
  cases eq
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa using functions_length hf
  · apply Array.toList_inj.mp
    simpa [Mir.Program.signatures, Program.signatures] using functions_signatures hf
  · intro i
    simpa using functions_lookup hf i

theorem program_wellFormed {p : Program} {out : Mir.Program}
    (h : WellFormedProgram p) (lowered : program p = some out) : out.WellFormed := by
  obtain ⟨schema, revision, profile, entry, count, sigs, lookup⟩ := program_metadata lowered
  refine ⟨schema, revision.trans h.revision, profile ▸ h.profile, ?_, ?_, ?_⟩
  · intro i hi
    have bound : i < p.functions.size := by simpa [count] using List.mem_range.mp hi
    let fn := p.functions[i]
    have hf : p.functions[i]? = some fn := Array.getElem?_eq_getElem bound
    have outbound : i < out.functions.size := by simpa [count] using bound
    let target := out.functions[i]
    have ht : out.functions[i]? = some target := Array.getElem?_eq_getElem outbound
    have lowerfn : function fn = some target := by simpa [hf, ht] using (lookup i).symm
    simp only [ht, Option.map_some, Option.some.injEq]
    exact (function_metadata lowerfn).1.trans (h.function_id hf)
  · obtain ⟨fn, hf, hv, hp, hr⟩ := h.entry
    obtain ⟨target, lowerfn, _⟩ := function_typed_total (h.function_at hf).body
    have ht : out.functions[out.entry]? = some target := by rw [entry, lookup, hf]; exact lowerfn
    have metadata :=  function_metadata lowerfn
    simp only [Mir.Program.EntryValid, ht]
    exact ⟨by simp [metadata.2.2.1, hv], by simp [metadata.2.2.2.1, hp, parameters], metadata.2.2.2.2.trans hr⟩
  · intro target ht
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
    have hi' : out.functions[i]? = some target := by simpa using hi
    have eq : (p.functions[i]?).bind function = some target := (lookup i).symm.trans hi'
    obtain ⟨fn, hf, lowerfn⟩ := Option.bind_eq_some_iff.mp eq
    rw [sigs]
    exact function_wellFormed (h.function_at hf) lowerfn

theorem program_total_wellFormed (h : WellFormedProgram p) :
    ∃ out, program p = some out ∧ out.WellFormed := by
  obtain ⟨out, lowered⟩ := program_total h
  exact ⟨out, lowered, program_wellFormed h lowered⟩

theorem checked_program_lowers (h : ANL.Memory.checkProgram p = true) :
    ∃ out, program p = some out ∧ Mir.checkProgram out = true := by
  obtain ⟨out, lowered, valid⟩ := program_total_wellFormed (ANL.Memory.checkProgram_iff.mp h)
  exact ⟨out, lowered, Mir.checkProgram_complete valid⟩

theorem program_deterministic {p : Program} {left right : Mir.Program}
    (hl : program p = some left) (hr : program p = some right) : left = right :=
  Option.some.inj (hl.symm.trans hr)

end ANL.Memory.Lowering
