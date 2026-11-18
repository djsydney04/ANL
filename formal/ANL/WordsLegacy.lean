import ANL.WordsLegacyCore
import ANL.WordsTyping
import ANL.MemoryTyping

namespace ANL.Words

private theorem flat_map_injective {f : α → β} (hf : ∀ x y, f x = f y → x = y)
    {a b : Flat α} (h : a.map f = b.map f) : a = b := by
  apply APL.FlatProducts.Flat.ext
  exact (List.map_inj_right hf).mp (congrArg APL.FlatProducts.Flat.fields h)

theorem embedTy_injective (h : embedTy a = embedTy b) : a = b := by
  cases a with
  | scalar a => cases b <;> simp_all [embedTy]
  | tuple a =>
    cases b with
    | scalar _ => cases h
    | tuple b =>
      exact congrArg APL.FlatProducts.Ty.tuple
        (flat_map_injective (fun _ _ => ScalarTy.legacy.inj) (Ty.tuple.inj h))

theorem embedVal_injective (h : embedVal a = embedVal b) : a = b := by
  cases a with
  | scalar a => cases b <;> simp_all [embedVal]
  | tuple a =>
    cases b with
    | scalar _ => cases h
    | tuple b =>
      exact congrArg APL.FlatProducts.Val.tuple
        (flat_map_injective (fun _ _ => ScalarVal.legacy.inj) (Val.tuple.inj h))

@[simp] theorem embedVal_type (v : APL.FlatProducts.Val) : (embedVal v).type = embedTy v.type := by
  cases v with
  | scalar v => rfl
  | tuple fields =>
    apply congrArg Ty.tuple
    apply APL.FlatProducts.Flat.ext
    simp [APL.FlatProducts.Flat.map,
      List.map_map, Function.comp_def, ScalarVal.type]

@[simp] theorem embedResult_typed : (embedResult r).Typed (embedTy t) ↔ r.Typed t := by
  cases r with
  | value v => exact ⟨fun h => embedTy_injective (embedVal_type v ▸ h), fun h => (embedVal_type v).trans (congrArg embedTy h)⟩
  | trap _ => rfl
  | invalid => rfl

@[simp] theorem legacy_shape_eq {a b : Flat APL.Ty} :
    a.map ScalarTy.legacy = b.map ScalarTy.legacy ↔ a = b :=
  ⟨flat_map_injective (fun _ _ => ScalarTy.legacy.inj), congrArg (APL.FlatProducts.Flat.map _)⟩

@[simp] theorem legacy_values_eq {a b : List APL.Val} :
    a.map ScalarVal.legacy = b.map ScalarVal.legacy ↔ a = b :=
  List.map_inj_right (fun _ _ => ScalarVal.legacy.inj)

theorem legacyResult_commutes (r : APL.Result) :
    legacyResult r = embedResult (APL.FlatProducts.embedResult r) := by
  cases r <;> rfl

theorem unary_commutes (op : APL.UOp) (v : APL.FlatProducts.Val) :
    unary (.legacy op) (embedVal v) = embedResult (APL.FlatProducts.unary op v) := by
  cases v with
  | scalar v => exact legacyResult_commutes _
  | tuple _ => rfl

theorem binaryType_commutes (op : APL.BOp) (a b : APL.FlatProducts.Ty) :
    binaryType (.legacy op) (embedTy a) (embedTy b) =
      (APL.FlatProducts.binaryType op a b).map embedTy := by
  cases a with
  | scalar a =>
    cases b with
    | scalar b => simp [binaryType, embedTy, APL.FlatProducts.binaryType, Option.map_map, Function.comp_def]
    | tuple b => rfl
  | tuple a =>
    cases b with
    | scalar b => rfl
    | tuple b =>
      cases op <;> simp [binaryType, embedTy, APL.FlatProducts.binaryType]

theorem legacy_shape_type (fields : Flat APL.Val) :
    (fields.map ScalarVal.legacy).map ScalarVal.type = (fields.map APL.Val.type).map ScalarTy.legacy := by
  apply APL.FlatProducts.Flat.ext
  simp [APL.FlatProducts.Flat.map, List.map_map, Function.comp_def, ScalarVal.type]

theorem binary_commutes (op : APL.BOp) (a b : APL.FlatProducts.Val) :
    binary (.legacy op) (embedVal a) (embedVal b) = embedResult (APL.FlatProducts.binary op a b) := by
  cases a with
  | scalar a =>
    cases b with
    | scalar b => exact legacyResult_commutes _
    | tuple _ => rfl
  | tuple a =>
    cases b with
    | scalar _ => rfl
    | tuple b =>
      simp only [binary, embedVal, APL.FlatProducts.binary, legacy_shape_type, legacy_shape_eq]
      by_cases ht : a.map APL.Val.type = b.map APL.Val.type
      · simp only [ht, ite_true]
        cases op <;> simp [embedResult, embedVal, APL.FlatProducts.Flat.map]
      · simp [ht, embedResult]

theorem shortCircuit_commutes (op : APL.BOp) (v : APL.FlatProducts.Val) :
    shortCircuit (.legacy op) (embedVal v) = APL.FlatProducts.shortCircuit op v := by
  cases v <;> rfl

theorem flat_make_map (f : α → β) (xs : List α) :
    APL.FlatProducts.Flat.make (xs.map f) = (APL.FlatProducts.Flat.make xs).map (APL.FlatProducts.Flat.map f) := by
  by_cases h : 0 < xs.length ∧ xs.length ≤ 8
  · simp [APL.FlatProducts.Flat.make, h]
    rfl
  · simp [APL.FlatProducts.Flat.make, h]

theorem construct_commutes (fields : List APL.Val) :
    construct (fields.map ScalarVal.legacy) = embedResult (APL.FlatProducts.construct fields) := by
  simp only [construct, flat_make_map, APL.FlatProducts.construct]
  cases APL.FlatProducts.Flat.make fields <;> rfl

theorem project_commutes (v : APL.FlatProducts.Val) (i : Nat) :
    project (embedVal v) i = embedResult (APL.FlatProducts.project v i) := by
  cases v with
  | scalar _ => rfl
  | tuple fields =>
    simp only [project, embedVal, APL.FlatProducts.project, APL.FlatProducts.Flat.map, List.getElem?_map]
    cases fields.fields[i]? <;> rfl

@[simp] theorem embedTerm_type (e : ANL.Memory.Term) : (embedTerm e).ty = embedTy e.ty := by
  cases e <;> simp [embedTerm, Term.ty, ANL.Memory.Term.ty]

@[simp] theorem embedTerm_heapSites (e : ANL.Memory.Term) : (embedTerm e).heapSites = e.heapSites := by
  induction e using ANL.Memory.Term.rec
    (motive_2 := fun es => (es.map embedTerm).flatMap Term.heapSites = es.flatMap ANL.Memory.Term.heapSites) <;>
    simp_all [embedTerm, Term.heapSites, ANL.Memory.Term.heapSites]

@[simp] theorem embedContext_cons (binding : APL.FlatProducts.Ty × Bool) (Γ : ANL.Memory.VCtx) :
    embedContext (binding :: Γ) = (embedTy binding.1, binding.2) :: embedContext Γ := rfl

theorem embedContext_lookup {i : Nat} (h : Γ[i]? = some (t, permission)) :
    (embedContext Γ)[i]? = some (embedTy t, permission) := by
  simp [embedContext, List.getElem?_map, h]

theorem embedSignatures_lookup {i : Nat} (h : sigs[i]? = some fn) :
    (embedSignatures sigs)[i]? = some (embedSignature fn) := by
  simp [embedSignatures, Array.getElem?_map, h]

@[simp] theorem embedFunction_signature (fn : ANL.Memory.Function) :
    (embedFunction fn).signature = embedSignature fn.signature := rfl

@[simp] theorem embedProgram_signatures (p : ANL.Memory.Program) :
    (embedProgram p).signatures = embedSignatures p.signatures := by
  simp [embedProgram, Program.signatures, embedSignatures, ANL.Memory.Program.signatures, Array.map_map]

@[simp] theorem embedFunction_valueContext (fn : ANL.Memory.Function) :
    (embedFunction fn).valueContext = embedContext fn.valueContext := by
  simp [embedFunction, Function.valueContext, ANL.Memory.Function.valueContext,
    immutable, APL.FlatProducts.immutable, embedContext, List.map_map, List.map_reverse, Function.comp_def]

@[simp] theorem embedFunction_resourceContext (fn : ANL.Memory.Function) :
    (embedFunction fn).resourceContext = fn.resourceContext := rfl

theorem embedEnv_typed (h : APL.FlatProducts.EnvTyped env Γ) : EnvTyped (embedEnv env) (embedContext Γ) := by
  simp only [EnvTyped, embedEnv, embedContext, List.map_map]
  have he := congrArg (List.map embedTy) h
  simpa only [List.map_map, Function.comp_def, embedVal_type] using he

theorem embedTerm_typed (h : ANL.Memory.HasType sigs Γ R e t) :
    HasType (embedSignatures sigs) (embedContext Γ) R (embedTerm e) (embedTy t) := by
  induction h using ANL.Memory.HasType.rec
    (motive_2 := fun Γ R es ts _ => ArgsTyped (embedSignatures sigs) (embedContext Γ) R
      (es.map embedTerm) (ts.map embedTy)) with
  | lit => simpa [embedTerm, embedTy] using (HasType.lit (sigs := embedSignatures sigs) (Γ := embedContext _) (R := _))
  | «local» hi => simpa [embedTerm] using HasType.local (R := _) (sigs := embedSignatures sigs) (embedContext_lookup hi)
  | letE _ _ ha hb => simpa [embedTerm] using HasType.letE ha hb
  | letMut _ _ ha hb => simpa [embedTerm] using HasType.letMut ha hb
  | assign hi _ ha => simpa [embedTerm, embedTy] using HasType.assign (embedContext_lookup hi) ha
  | whileE _ _ hc hb => simpa [embedTerm, embedTy] using HasType.whileE hc hb
  | ifE _ _ _ hc ha hb => simpa [embedTerm, embedTy] using HasType.ifE hc ha hb
  | unary _ ha => simpa [embedTerm, embedTy] using HasType.unary ha UnarySig.legacy
  | binary _ _ hop ha hb =>
    have hs := binaryType_iff.mp (by rw [binaryType_commutes, hop]; rfl)
    simpa [embedTerm] using HasType.binary ha hb hs
  | call hf hv _ ha =>
    simpa [embedTerm, embedSignature] using HasType.call (embedSignatures_lookup hf) hv ha
  | tuple _ ih =>
    simp only [embedTerm, embedTy]
    apply HasType.tuple
    simpa [APL.FlatProducts.Flat.map, List.map_map, Function.comp_def, embedTy] using ih
  | project _ hi ih =>
    simp only [embedTerm, embedTy]
    apply HasType.project ih
    simpa only [APL.FlatProducts.Flat.map, List.getElem?_map, Option.map_some] using
      congrArg (Option.map ScalarTy.legacy) hi
  | heap _ _ _ _ hl hi hs hf => simpa [embedTerm, embedTy] using HasType.heap hl hi hs hf
  | bufferLength hr => simpa [embedTerm, embedTy] using HasType.bufferLength (sigs := embedSignatures sigs) (Γ := embedContext _) hr
  | bufferRead hr _ hi => simpa [embedTerm, embedTy] using HasType.bufferRead hr hi
  | bufferWrite hr hm _ _ hi hv => simpa [embedTerm, embedTy] using HasType.bufferWrite hr hm hi hv
  | callView hf hm hr hp _ ha =>
    simpa [embedTerm, embedSignature] using HasType.callView (embedSignatures_lookup hf) hm hr hp ha
  | nil => exact .nil
  | cons _ _ ha hb => exact .cons ha hb

theorem embedFunction_wellFormed (h : fn.WellFormed sigs) :
    (embedFunction fn).WellFormed (embedSignatures sigs) := by
  constructor
  · exact h.name
  · simpa only [Term.CanonicalSites, ANL.Memory.Term.CanonicalSites, embedFunction, embedTerm_heapSites] using h.sites
  · change HasType (embedSignatures sigs) (embedFunction fn).valueContext fn.resourceContext (embedTerm fn.body) (embedTy fn.result)
    rw [embedFunction_valueContext]
    exact embedTerm_typed h.body

theorem embedProgram_wellFormed (h : ANL.Memory.WellFormedProgram p) : WellFormedProgram (embedProgram p) := by
  constructor
  · rfl
  · rfl
  · exact h.profile
  · simpa [embedProgram, embedFunction, List.map_map, Function.comp_def] using h.ids
  · simpa [embedProgram, embedFunction, List.map_map, Function.comp_def] using h.names
  · intro fn hf
    simp only [embedProgram, Array.toList_map, List.mem_map] at hf
    obtain ⟨old, hold, rfl⟩ := hf
    rw [embedProgram_signatures]
    exact embedFunction_wellFormed (h.functions old hold)
  · obtain ⟨fn, hf, hv, ha, ht⟩ := h.entry
    refine ⟨embedFunction fn, ?_, hv, ?_, ?_⟩
    · simp [embedProgram, Array.getElem?_map, hf]
    · simp [embedFunction, ha]
    · simp [embedFunction, ht, embedTy]

theorem embedProgram_checked (h : ANL.Memory.checkProgram p = true) : checkProgram (embedProgram p) = true :=
  checkProgram_iff.mpr (embedProgram_wellFormed (ANL.Memory.checkProgram_iff.mp h))

@[simp] theorem embedTy_eq {a b : APL.FlatProducts.Ty} : embedTy a = embedTy b ↔ a = b :=
  ⟨embedTy_injective, congrArg embedTy⟩

theorem embedTerm_injective (h : embedTerm a = embedTerm b) : a = b := by
  induction a using ANL.Memory.Term.rec
    (motive_2 := fun es => ∀ bs, es.map embedTerm = bs.map embedTerm → es = bs) generalizing b
  case nil bs he => cases bs <;> simp_all
  case cons a es ia ies bs he => cases bs <;> simp_all <;> grind
  all_goals cases b <;> simp_all [embedTerm] <;> grind

end ANL.Words
