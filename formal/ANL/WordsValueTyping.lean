import ANL.WordsValues

namespace ANL.Words

theorem i64_range_iff (n : Int) : ANL.Word.I64Range n ↔ APL.InRange n := Iff.rfl

theorem wordLiteralType_iff : wordLiteralType width value = some t ↔ WordLiteralSig width value t := by
  constructor
  · intro h
    unfold wordLiteralType at h
    cases hw : ANL.Word.Width.decode width with
    | none => simp [hw] at h
    | some w =>
      simp only [hw, bind, Option.bind_some] at h
      split at h
      next hv =>
        cases h
        exact .word ((ANL.Word.Width.decode_iff _ _).mp hw) hv
      · contradiction
  · intro h
    cases h with
    | word hw hv =>
      have hd := (ANL.Word.Width.decode_iff _ _).mpr hw
      simp [wordLiteralType, hd, hv]

theorem unaryType_iff : unaryType op a = some t ↔ UnarySig op a t := by
  constructor
  · intro h
    cases op with
    | legacy op =>
      cases a with
      | tuple _ => simp [unaryType] at h
      | scalar a =>
        cases a with
        | word _ => simp [unaryType] at h
        | legacy a =>
          simp only [unaryType] at h
          split at h
          next ha => subst a; cases h; exact .legacy
          · contradiction
    | bitNot =>
      cases a with
      | tuple _ => simp [unaryType] at h
      | scalar a =>
        cases a with
        | legacy _ => simp [unaryType] at h
        | word _ => cases h; exact .bitNot
  · intro h
    cases h <;> simp [unaryType]

theorem arithmetic_compare_disjoint (ha : WordArithmeticOp op) : ¬ WordCompareOp op := by
  cases op with
  | legacy op => cases op <;> simp_all [WordArithmeticOp, WordCompareOp]
  | _ => simp_all [WordArithmeticOp, WordCompareOp]

theorem arithmetic_lookup_iff (op : BOp) : WordArithmeticOp op ↔ ∃ operation, wordArithmetic op = some operation := by
  cases op with
  | legacy op => cases op <;> simp [WordArithmeticOp, wordArithmetic]
  | _ => simp [WordArithmeticOp, wordArithmetic]

theorem compare_lookup_iff (op : BOp) (a b : Nat) : WordCompareOp op ↔ ∃ value, compareWord op a b = some value := by
  cases op with
  | legacy op => cases op <;> simp [WordCompareOp, compareWord] <;> exact Classical.em _
  | _ => simp [WordCompareOp, compareWord]

theorem compare_arithmetic_none (h : WordCompareOp op) : wordArithmetic op = none := by
  cases op with
  | legacy op => cases op <;> simp_all [WordCompareOp, wordArithmetic]
  | _ => simp_all [WordCompareOp]

theorem binaryType_iff : binaryType op a b = some t ↔ BinarySig op a b t := by
  constructor
  · intro h
    cases a with
    | scalar a =>
      cases b with
      | tuple _ => simp [binaryType] at h
      | scalar b =>
        cases a with
        | legacy a =>
          cases b with
          | word _ => simp [binaryType] at h
          | legacy b =>
            cases op with
            | legacy op =>
              obtain ⟨t, hop, rfl⟩ := Option.map_eq_some_iff.mp h
              exact .legacy hop
            | _ => simp [binaryType] at h
        | word a =>
          cases b with
          | legacy b =>
            cases b with
            | bool | unit => simp [binaryType] at h
            | i64 =>
              simp only [binaryType] at h
              split at h
              next hop => cases h; exact .shift hop
              · contradiction
          | word b =>
            simp only [binaryType] at h
            split at h
            next hw =>
              subst b
              split at h
              next ha => cases h; exact .arithmetic ha
              next _ =>
                split at h
                next hc => cases h; exact .compare hc
                · contradiction
            · contradiction
    | tuple a =>
      cases b with
      | scalar _ => simp [binaryType] at h
      | tuple b =>
        simp only [binaryType] at h
        split at h
        next he =>
          obtain ⟨hop, rfl⟩ := he
          cases h
          exact .tuple hop
        · contradiction
  · intro h
    cases h with
    | legacy hop => simp [binaryType, hop]
    | arithmetic hop => simp [binaryType, hop]
    | compare hop =>
      have ha : ¬ WordArithmeticOp _ := fun h => arithmetic_compare_disjoint h hop
      simp [binaryType, ha, hop]
    | shift hop => simp [binaryType, hop]
    | tuple hop => simp [binaryType, hop]

theorem convertType_iff : convertType mode target source = some t ↔ ConvertSig mode target source t := by
  constructor
  · intro h
    cases source with
    | tuple _ => simp [convertType] at h
    | scalar source =>
      simp only [convertType] at h
      split at h
      next condition => cases h; exact .numeric condition.1 condition.2.1 condition.2.2
      · contradiction
  · intro h
    cases h with
    | numeric hs ht hm => simp [convertType, hs, ht, hm]

theorem scalar_canonical {v : Val} {t : ScalarTy} (h : v.type = .scalar t) :
    ∃ a, v = .scalar a ∧ a.type = t := by
  cases v with
  | scalar a => exact ⟨a, rfl, Ty.scalar.inj h⟩
  | tuple fields => cases h

theorem tuple_canonical {v : Val} {shape : Flat ScalarTy} (h : v.type = .tuple shape) :
    ∃ fields, v = .tuple fields ∧ fields.map ScalarVal.type = shape := by
  cases v with
  | scalar a => cases h
  | tuple fields => exact ⟨fields, rfl, Ty.tuple.inj h⟩

theorem scalar_legacy_canonical {v : ScalarVal} (h : v.type = .legacy t) :
    ∃ a, v = .legacy a ∧ a.type = t := by
  cases v with
  | legacy a => exact ⟨a, rfl, ScalarTy.legacy.inj h⟩
  | word a => cases h

theorem scalar_word_canonical {v : ScalarVal} (h : v.type = .word w) :
    ∃ a, v = .word a ∧ a.val.width = w := by
  cases v with
  | legacy a => cases h
  | word a => exact ⟨a, rfl, ScalarTy.word.inj h⟩

theorem legacyResult_typed (h : r.Typed t) : (legacyResult r).Typed (.scalar (.legacy t)) := by
  cases r with
  | value v => exact congrArg (fun t => Ty.scalar (.legacy t)) h
  | trap _ => trivial
  | invalid => exact h

theorem wordResult_typed (hn : r ≠ .invalidInput)
    (hv : ∀ v, r = .value v → ANL.Word.Valid v ∧ v.width = w) :
    (wordResult r).Typed (.scalar (.word w)) := by
  cases r with
  | invalidInput => exact False.elim (hn rfl)
  | trap _ => trivial
  | value v =>
    obtain ⟨valid, width⟩ := hv v rfl
    simp [wordResult, valid, Result.Typed, Val.type, ScalarVal.type, width]

theorem signedResult_typed (hn : r ≠ .invalidInput)
    (hv : ∀ v, r = .value v → APL.InRange v) :
    (signedResult r).Typed (.scalar (.legacy .i64)) := by
  cases r with
  | invalidInput => exact False.elim (hn rfl)
  | trap _ => trivial
  | value v => simp [signedResult, hv v rfl, Result.Typed, Val.type, ScalarVal.type, APL.Val.type]

theorem wordBinary_typed (op : ANL.Word.BinaryOp) (a b : WordValue) (hw : a.val.width = b.val.width) :
    (wordResult (ANL.Word.binary op a.val b.val)).Typed (.scalar (.word a.val.width)) := by
  apply wordResult_typed
  · intro h
    exact (ANL.Word.binary_invalid_iff _ _ _).mp h ⟨a.property, b.property, hw⟩
  · intro v h
    have facts := (ANL.Word.binary_value_iff _ _ _ _).mp h
    exact ⟨facts.2.2.1, facts.2.1⟩

theorem wordShift_typed (op : ANL.Word.ShiftOp) (a : WordValue) (n : APL.I64) :
    (wordResult (ANL.Word.shift op a.val n.val)).Typed (.scalar (.word a.val.width)) := by
  apply wordResult_typed
  · intro h
    exact (ANL.Word.shift_invalid_iff _ _ _).mp h ⟨a.property, (i64_range_iff _).mpr n.property⟩
  · intro v h
    exact ⟨ANL.Word.shift_value_valid h, ((ANL.Word.shift_value_iff _ _ _ _).mp h).2.2.2.1⟩

theorem wordLiteral_typed (h : WordLiteralSig width value t) : (wordLiteral width value).Typed t := by
  cases h with
  | @word w hw hv =>
    have decoded : ANL.Word.decodeLiteral width value = some ⟨w, value⟩ :=
      (ANL.Word.decodeLiteral_iff _ _ _).mpr ⟨hw, rfl, hv⟩
    simp [wordLiteral, decoded, wordResult, ANL.Word.Valid, hv, Result.Typed, Val.type, ScalarVal.type]

theorem unary_typed (h : UnarySig op a.type t) : (unary op a).Typed t := by
  generalize ha : a.type = source at h
  cases h with
  | legacy =>
    obtain ⟨v, rfl, hv1⟩ := scalar_canonical ha
    obtain ⟨v, rfl, hv2⟩ := scalar_legacy_canonical hv1
    exact legacyResult_typed (APL.unary_typed hv2)
  | bitNot =>
    obtain ⟨v, rfl, hv1⟩ := scalar_canonical ha
    obtain ⟨v, rfl, hv2⟩ := scalar_word_canonical hv1
    apply wordResult_typed
    · intro h
      exact (ANL.Word.complement_invalid_iff _).mp h v.property
    · intro result hr
      exact ⟨ANL.Word.complement_value_valid hr,
        ((ANL.Word.complement_value_iff _ _).mp hr).2.1.trans hv2⟩

theorem binary_typed (h : BinarySig op a.type b.type t) : (binary op a b).Typed t := by
  generalize ha : a.type = left at h
  generalize hb : b.type = right at h
  cases h with
  | legacy hop =>
    obtain ⟨a, rfl, ha1⟩ := scalar_canonical ha
    obtain ⟨b, rfl, hb1⟩ := scalar_canonical hb
    obtain ⟨a, rfl, ha2⟩ := scalar_legacy_canonical ha1
    obtain ⟨b, rfl, hb2⟩ := scalar_legacy_canonical hb1
    exact legacyResult_typed (APL.binary_typed (ha2 ▸ hb2 ▸ hop))
  | arithmetic hop =>
    obtain ⟨a, rfl, ha1⟩ := scalar_canonical ha
    obtain ⟨b, rfl, hb1⟩ := scalar_canonical hb
    obtain ⟨a, rfl, ha2⟩ := scalar_word_canonical ha1
    obtain ⟨b, rfl, hb2⟩ := scalar_word_canonical hb1
    have hw := ha2.trans hb2.symm
    obtain ⟨operation, hop⟩ := (arithmetic_lookup_iff _).mp hop
    simpa only [binary, hw, ite_true, hop, hb2] using wordBinary_typed operation a b hw
  | compare hop =>
    obtain ⟨a, rfl, ha1⟩ := scalar_canonical ha
    obtain ⟨b, rfl, hb1⟩ := scalar_canonical hb
    obtain ⟨a, rfl, ha2⟩ := scalar_word_canonical ha1
    obtain ⟨b, rfl, hb2⟩ := scalar_word_canonical hb1
    have hw := ha2.trans hb2.symm
    have hn := compare_arithmetic_none hop
    obtain ⟨result, hr⟩ := (compare_lookup_iff _ a.val.value b.val.value).mp hop
    simp [binary, hw, hn, hr, Result.Typed, Val.type, ScalarVal.type, APL.Val.type]
  | shift hop =>
    obtain ⟨a, rfl, ha1⟩ := scalar_canonical ha
    obtain ⟨b, rfl, hb1⟩ := scalar_canonical hb
    obtain ⟨a, rfl, ha2⟩ := scalar_word_canonical ha1
    obtain ⟨b, rfl, hb2⟩ := scalar_legacy_canonical hb1
    cases b with
    | bool _ | unit => cases hb2
    | int n =>
      rcases hop with rfl | rfl
      · simpa only [binary, ha2] using wordShift_typed .left a n
      · simpa only [binary, ha2] using wordShift_typed .right a n
  | tuple hop =>
    obtain ⟨a, rfl, ha2⟩ := tuple_canonical ha
    obtain ⟨b, rfl, hb2⟩ := tuple_canonical hb
    have hw := ha2.trans hb2.symm
    rcases hop with rfl | rfl <;>
      simp [binary, hw, Result.Typed, Val.type, ScalarVal.type, APL.Val.type]

theorem checkedFromI64_typed (w : ANL.Word.Width) (n : APL.I64) :
    (wordResult (ANL.Word.checkedFromI64 w n.val)).Typed (.scalar (.word w)) := by
  apply wordResult_typed
  · intro h
    exact (ANL.Word.checkedFromI64_invalid_iff _ _).mp h ((i64_range_iff _).mpr n.property)
  · intro v h
    exact ⟨ANL.Word.checkedFromI64_value_valid h, ((ANL.Word.checkedFromI64_value_iff _ _ _).mp h).2.1⟩

theorem truncateFromI64_typed (w : ANL.Word.Width) (n : APL.I64) :
    (wordResult (ANL.Word.truncateFromI64 w n.val)).Typed (.scalar (.word w)) := by
  apply wordResult_typed
  · intro h
    exact (ANL.Word.truncateFromI64_invalid_iff _ _).mp h ((i64_range_iff _).mpr n.property)
  · intro v h
    exact ⟨ANL.Word.truncateFromI64_value_valid h, ((ANL.Word.truncateFromI64_value_iff _ _ _).mp h).2.1⟩

theorem checkedWordCast_typed (w : ANL.Word.Width) (a : WordValue) :
    (wordResult (ANL.Word.checkedWordCast w a.val)).Typed (.scalar (.word w)) := by
  apply wordResult_typed
  · intro h
    exact (ANL.Word.checkedWordCast_invalid_iff _ _).mp h a.property
  · intro v h
    exact ⟨ANL.Word.checkedWordCast_value_valid h, ((ANL.Word.checkedWordCast_value_iff _ _ _).mp h).2.1⟩

theorem truncateWordCast_typed (w : ANL.Word.Width) (a : WordValue) :
    (wordResult (ANL.Word.truncateWordCast w a.val)).Typed (.scalar (.word w)) := by
  apply wordResult_typed
  · intro h
    exact (ANL.Word.truncateWordCast_invalid_iff _ _).mp h a.property
  · intro v h
    exact ⟨ANL.Word.truncateWordCast_value_valid h, ((ANL.Word.truncateWordCast_value_iff _ _ _).mp h).2.1⟩

theorem checkedToI64_typed (a : WordValue) :
    (signedResult (ANL.Word.checkedToI64 a.val)).Typed (.scalar (.legacy .i64)) := by
  apply signedResult_typed
  · intro h
    exact (ANL.Word.checkedToI64_invalid_iff _).mp h a.property
  · intro v h
    exact (i64_range_iff _).mp (ANL.Word.checkedToI64_value_range h)

theorem convert_typed (h : ConvertSig mode target a.type t) : (convert mode target a).Typed t := by
  generalize ha : a.type = source at h
  cases h with
  | numeric hs ht hm =>
    obtain ⟨a, rfl, ha⟩ := scalar_canonical ha
    cases a with
    | legacy a =>
      cases a with
      | bool _ | unit => cases ha; contradiction
      | int n =>
        cases target with
        | legacy target =>
          cases target with
          | bool | unit => contradiction
          | i64 =>
            have hm : mode = .checked := hm.resolve_right (by simp [IsWord])
            subst mode
            rfl
        | word w =>
          cases mode with
          | checked => exact checkedFromI64_typed w n
          | truncate => exact truncateFromI64_typed w n
    | word a =>
      cases target with
      | legacy target =>
        cases target with
        | bool | unit => contradiction
        | i64 =>
          have hm : mode = .checked := hm.resolve_right (by simp [IsWord])
          subst mode
          exact checkedToI64_typed a
      | word w =>
        cases mode with
        | checked => exact checkedWordCast_typed w a
        | truncate => exact truncateWordCast_typed w a

theorem shortCircuit_typed (h : BinarySig op v.type b t)
    (hs : shortCircuit op v = true) : v.type = t := by
  have h := binaryType_iff.mpr h
  cases v with
  | tuple _ => simp [shortCircuit] at hs
  | scalar v =>
    cases v with
    | word _ => simp [shortCircuit] at hs
    | legacy v =>
      cases op with
      | legacy op =>
        cases b with
        | tuple _ => simp [Val.type, ScalarVal.type, binaryType] at h
        | scalar b =>
          cases b with
          | word _ => simp [Val.type, ScalarVal.type, binaryType] at h
          | legacy b =>
            obtain ⟨ty, hop, rfl⟩ := Option.map_eq_some_iff.mp h
            exact congrArg (fun t => Ty.scalar (.legacy t)) (APL.shortCircuit_typed hop hs)
      | _ => simp [shortCircuit] at hs

theorem construct_typed (h : fields.map ScalarVal.type = shape.fields) :
    (construct fields).Typed (.tuple shape) := by
  have n : 0 < fields.length := by simpa [← h] using shape.nonempty
  have b : fields.length ≤ 8 := by simpa [← h] using shape.bounded
  simp only [construct, APL.FlatProducts.Flat.make, n, b, and_self, ↓reduceDIte, Result.Typed, Val.type]
  congr 1
  exact APL.FlatProducts.Flat.ext h

theorem project_typed (h : v.type = .tuple shape) (hi : shape.fields[index]? = some t) :
    (project v index).Typed (.scalar t) := by
  obtain ⟨fields, rfl, shape⟩ := tuple_canonical h
  subst shape
  simp only [APL.FlatProducts.Flat.map, List.getElem?_map] at hi
  cases hv : fields.fields[index]? with
  | none => simp [hv] at hi
  | some v =>
    simp only [hv, Option.map_some, Option.some.injEq] at hi
    simpa [project, hv, Result.Typed, Val.type] using congrArg Ty.scalar hi

theorem scalarList_complete (ts : List ScalarTy) :
    (ts.map Ty.scalar).mapM Ty.asScalar = some ts := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp [List.mapM_cons, Ty.asScalar, ih]

theorem scalarList_sound {ts : List Ty} {scalars : List ScalarTy}
    (h : ts.mapM Ty.asScalar = some scalars) : ts = scalars.map Ty.scalar := by
  induction ts generalizing scalars with
  | nil => simp at h; subst scalars; rfl
  | cons a ts ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨t, ht, rest, hr, h⟩ := h
    cases h
    cases a with
    | scalar a => simp only [Ty.asScalar, Option.some.injEq] at ht; subst t; simp [ih hr]
    | tuple shape => simp [Ty.asScalar] at ht

theorem make_fields {xs : List α} {shape : Flat α} (h : APL.FlatProducts.Flat.make xs = some shape) :
    shape.fields = xs := by
  unfold APL.FlatProducts.Flat.make at h
  split at h
  · cases h; rfl
  · contradiction

theorem env_cons (h : EnvTyped env Γ) : EnvTyped (v :: env) ((v.type, permission) :: Γ) := by
  simpa [EnvTyped] using h

theorem env_tail (h : EnvTyped (v :: env) (binding :: Γ)) : EnvTyped env Γ := by
  simpa [EnvTyped] using (List.cons.inj h).2

theorem env_lookup {i : Nat} {t : Ty} {permission : Bool} (h : EnvTyped env Γ) (hi : Γ[i]? = some (t, permission)) :
    ∃ v : Val, env[i]? = some v ∧ v.type = t := by
  have eq := congrArg (fun xs => xs[i]?) h
  simp only [List.getElem?_map, hi, Option.map_some] at eq
  cases hv : env[i]? with
  | none => simp [hv] at eq
  | some v => exact ⟨v, rfl, by simpa [hv] using eq⟩

theorem update_typed (h : EnvTyped env Γ) (hi : Γ[i]? = some (v.type, permission)) :
    ∃ env', update env i v = some env' ∧ EnvTyped env' Γ := by
  induction env generalizing Γ i with
  | nil => cases Γ <;> simp_all [EnvTyped]
  | cons a env ih =>
    cases Γ with
    | nil => simp [EnvTyped] at h
    | cons binding Γ =>
      have tail := env_tail h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst binding
        exact ⟨v :: env, rfl, env_cons tail⟩
      | succ i =>
        obtain ⟨env', hu, ht⟩ := ih tail hi
        exact ⟨a :: env', by simp [update, hu], by
          change a.type :: env'.map Val.type = binding.fst :: Γ.map Prod.fst
          rw [(List.cons.inj h).1, ht]⟩

theorem update_other (h : update env i v = some env') (different : j ≠ i) : env'[j]? = env[j]? := by
  induction env generalizing env' i j with
  | nil => simp [update] at h
  | cons a env ih =>
    cases i with
    | zero =>
      simp only [update, Option.some.injEq] at h
      subst env'
      cases j with
      | zero => exact False.elim (different rfl)
      | succ j => rfl
    | succ i =>
      simp only [update, Option.map_eq_some_iff] at h
      obtain ⟨rest, hr, rfl⟩ := h
      cases j with
      | zero => rfl
      | succ j => exact ih hr (fun eq => different (congrArg Nat.succ eq))

/-- A checked assignment cannot select any statically immutable binding. -/
theorem immutable_unchanged {Γ : VCtx} {i j : Nat} {t u : Ty} (hi : Γ[i]? = some (t, true))
    (hj : Γ[j]? = some (u, false)) (h : update env i v = some env') : env'[j]? = env[j]? := by
  apply update_other h
  intro eq
  subst j
  rw [hi] at hj
  cases hj

theorem Result.Typed.not_invalid {result : Result} (h : result.Typed t) : result ≠ .invalid := by
  intro he
  subst result
  exact h

theorem unary_not_invalid (h : UnarySig op a.type t) : unary op a ≠ .invalid :=
  (unary_typed h).not_invalid

theorem binary_not_invalid (h : BinarySig op a.type b.type t) : binary op a b ≠ .invalid :=
  (binary_typed h).not_invalid

theorem convert_not_invalid (h : ConvertSig mode target a.type t) : convert mode target a ≠ .invalid :=
  (convert_typed h).not_invalid

theorem wordLiteral_not_invalid (h : WordLiteralSig width value t) : wordLiteral width value ≠ .invalid :=
  (wordLiteral_typed h).not_invalid

end ANL.Words
