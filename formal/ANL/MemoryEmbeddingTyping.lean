import ANL.MemoryEmbedding

namespace ANL.Memory.Embedding

variable {sigs : OldSignatures} {context : VCtx} {resources : RCtx} {e : OldTerm} {ty : Ty}

theorem inferred_typed (h : APL.FlatProducts.HasType sigs context e ty) :
    inferred sigs context e = ty := by
  simp [inferred, APL.FlatProducts.infer_complete h]

theorem scalar_literals_typed {newSigs : Signatures} (values : List APL.Val) :
    ArgsTyped newSigs context resources (values.map scalarLiteral)
      (values.map (fun value => APL.FlatProducts.Ty.scalar value.type)) := by
  induction values with
  | nil => exact .nil
  | cons v vs ih => exact .cons .lit ih

theorem literal_typed {newSigs : Signatures} (value : Val) : HasType newSigs context resources (literal value) value.type := by
  cases value with
  | scalar value => exact .lit
  | tuple fields =>
      apply HasType.tuple
      simpa [APL.FlatProducts.Flat.map, List.map_map, Function.comp_def] using
        (scalar_literals_typed (newSigs := newSigs) (context := context) (resources := resources) fields.fields)

theorem term_related (e : OldTerm) (sigs : OldSignatures) (context : VCtx) :
    TermRel e (term sigs context e) := by
  induction e using APL.FlatProducts.Term.rec
    (motive_2 := fun args => ∀ context, TermsRel args (args.map (term sigs context))) generalizing context <;> (try simp only [term])
  case lit => exact .lit
  case «local» => exact .local
  case letE _ _ ihv ihb => exact .letE (ihv _) (ihb _)
  case letMut _ _ ihv ihb => exact .letMut (ihv _) (ihb _)
  case assign _ _ ih => exact .assign (ih _)
  case whileE _ _ ihc ihb => exact .whileE (ihc _) (ihb _)
  case ifE _ _ _ ihc ihy ihn => exact .ifE (ihc _) (ihy _) (ihn _)
  case unary _ _ ih => exact .unary (ih _)
  case binary _ _ _ ihl ihr => exact .binary (ihl _) (ihr _)
  case call _ _ ih => exact .call (ih _)
  case tuple _ ih => exact .tuple (ih _)
  case project _ _ ih => exact .project (ih _)
  case nil => exact .nil
  case cons head tail ihh iht context => exact .cons (ihh context) (iht context)

theorem literal_no_sites (value : Val) : (literal value).heapSites = [] := by
  cases value with
  | scalar value => simp [literal, scalarLiteral, Term.heapSites]
  | tuple fields =>
      simp [literal, Term.heapSites, List.flatMap_map, scalarLiteral]

theorem related_no_sites (h : TermRel e translated) : translated.heapSites = [] := by
  induction h using TermRel.rec
    (motive_2 := fun _ translated _ => translated.flatMap Term.heapSites = []) <;>
    simp_all [Term.heapSites, literal_no_sites]

theorem term_no_sites (e : OldTerm) : (term sigs context e).heapSites = [] :=
  related_no_sites (term_related e sigs context)

theorem term_typed (h : APL.FlatProducts.HasType sigs context e ty) :
    HasType (signatures sigs) context resources (term sigs context e) ty := by
  induction h using APL.FlatProducts.HasType.rec
    (motive_2 := fun context args types _ =>
      ArgsTyped (signatures sigs) context resources (args.map (term sigs context)) types) with
  | lit => simpa only [term] using literal_typed _
  | «local» hi =>
      simpa only [term, inferred_typed (.local hi)] using (HasType.local hi (R := resources) (sigs := signatures sigs))
  | letE ha hb ia ib =>
      simpa only [term, inferred_typed (.letE ha hb), inferred_typed ha] using HasType.letE ia ib
  | letMut ha hb ia ib =>
      simpa only [term, inferred_typed (.letMut ha hb), inferred_typed ha] using HasType.letMut ia ib
  | assign hi ha ia =>
      simpa only [term, inferred_typed (.assign hi ha)] using HasType.assign hi ia
  | whileE hc hb ic ib =>
      simpa only [term, inferred_typed (.whileE hc hb)] using HasType.whileE ic ib
  | ifE hc hy hn ic iy ino =>
      simpa only [term, inferred_typed (.ifE hc hy hn)] using HasType.ifE ic iy ino
  | unary ha ia =>
      simpa only [term, inferred_typed (.unary ha)] using HasType.unary ia
  | binary ha hb hop ia ib =>
      simpa only [term, inferred_typed (.binary ha hb hop)] using HasType.binary ia ib hop
  | @call f params result Γ args hf ha ia =>
      have lookup : (signatures sigs)[f]? = some (Signature.mk none params result) := by
        simp [signatures, Array.getElem?_map, hf]
      simpa only [term, inferred_typed (.call hf ha)] using HasType.call lookup rfl ia
  | tuple ha ia =>
      simpa only [term, inferred_typed (.tuple ha)] using HasType.tuple ia
  | project hb hi ib =>
      simpa only [term, inferred_typed (.project hb hi)] using HasType.project ib hi
  | nil => exact .nil
  | cons _ _ ihh iht => exact .cons ihh iht

theorem functions_lookup (fs : OldFunctions) (id : Nat) :
    (functions fs)[id]? = fs[id]?.map (function (APL.FlatProducts.signatures fs) id) := by
  simp [functions, Array.getElem?_mapIdx]

theorem functions_signatures (fs : OldFunctions) :
    (functions fs).map Function.signature = signatures (APL.FlatProducts.signatures fs) := by
  apply Array.ext
  · simp [functions, signatures, APL.FlatProducts.signatures]
  · intro i hi hj
    simp [functions, signatures, APL.FlatProducts.signatures, Function.signature, function]

theorem functions_ids (fs : OldFunctions) :
    (functions fs).toList.map Function.id = List.range (functions fs).size := by
  simpa only [functions, Array.toList_mapIdx, Array.size_mapIdx, List.mapIdx_eq_zipIdx_map,
    List.map_map, Function.comp_def, function, ← List.range_eq_range', Array.length_toList] using
    List.zipIdx_map_snd 0 fs.toList

theorem functions_names (fs : OldFunctions) :
    (functions fs).toList.map Function.name = fs.toList.map APL.FlatProducts.Function.name := by
  apply List.ext_getElem?
  intro i
  simp [functions, List.getElem?_map, function, Option.map_map, Function.comp_def]

theorem functions_related (fs : OldFunctions) (profile : Profile) (entry : Nat) :
    FunctionsRel fs (program fs profile entry) := by
  constructor
  · intro i fn hi
    refine ⟨function (APL.FlatProducts.signatures fs) i fn, ?_, rfl, term_related ..⟩
    simp [program, functions_lookup, hi]
  · intro i hi
    simp [program, functions_lookup, hi]

theorem function_typed {fs : OldFunctions} {id : Nat} {fn : OldFunction} (h : APL.FlatProducts.WellTyped fs) (lookup : fs[id]? = some fn) :
    HasType (signatures (APL.FlatProducts.signatures fs))
      (function (APL.FlatProducts.signatures fs) id fn).valueContext []
      (function (APL.FlatProducts.signatures fs) id fn).body fn.result := by
  exact term_typed (h id fn lookup)

theorem program_wellFormed (fs : OldFunctions) (profile : Profile) (entry : Nat)
    (typed : APL.FlatProducts.WellTyped fs)
    (profileValid : profile.Admissible)
    (namesValid : ∀ fn ∈ fs.toList, ValidName fn.name)
    (namesUnique : (fs.toList.map APL.FlatProducts.Function.name).Nodup)
    (entryValid : ∃ fn, fs[entry]? = some fn ∧ fn.params = [] ∧ fn.result = .scalar .i64) :
    WellFormedProgram (program fs profile entry) := by
  refine ⟨rfl, rfl, profileValid, functions_ids fs, ?_, ?_, ?_⟩
  · simpa only [program, functions_names] using namesUnique
  · intro translated member
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp member
    have hi : (functions fs)[i]? = some translated := by simpa only [program, Array.getElem?_toList] using hi
    rw [functions_lookup] at hi
    obtain ⟨fn, hf, rfl⟩ := Option.map_eq_some_iff.mp hi
    constructor
    · apply namesValid fn
      exact List.mem_iff_getElem?.mpr ⟨i, by simpa using hf⟩
    · simp [function, Term.CanonicalSites, term_no_sites]
    · simpa only [program, Program.signatures, functions_signatures,
        function, Function.valueContext, Function.resourceContext, viewContext] using
        term_typed (resources := []) (typed i fn hf)
  · obtain ⟨fn, hf, hp, hr⟩ := entryValid
    refine ⟨function (APL.FlatProducts.signatures fs) entry fn, ?_, rfl, hp, hr⟩
    simp [program, functions_lookup, hf]

end ANL.Memory.Embedding
