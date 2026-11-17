import APL.ProductLogicScalar
import APL.FlatProductsValues

namespace APL.ProductLogic

open VCG (MVal Model)
open FlatProducts (Flat)

inductive MValue where
  | scalar (value : MVal)
  | tuple (fields : Flat MVal)
  deriving DecidableEq, Repr

def MValue.type : MValue → FlatProducts.Ty
  | .scalar v => .scalar v.type
  | .tuple fields => .tuple (fields.map MVal.type)

def embedValue : FlatProducts.Val → MValue
  | .scalar v => .scalar (VCG.embed v)
  | .tuple fields => .tuple (fields.map VCG.embed)

@[simp] theorem embed_scalar_type (v : APL.Val) : (VCG.embed v).type = v.type := by
  cases v <;> rfl

@[simp] theorem embedValue_type (v : FlatProducts.Val) : (embedValue v).type = v.type := by
  cases v with
  | scalar v => simp [embedValue, MValue.type, FlatProducts.Val.type]
  | tuple fields =>
      simp only [embedValue, MValue.type, FlatProducts.Val.type]
      congr 1
      apply Flat.ext
      simp [Flat.map, List.map_map, Function.comp_def]

structure SymScalar where
  type : APL.Ty
  term : SymTerm
  unit_literal : type = .unit → term = .lit .unit
  deriving Repr

def SymScalar.literal (value : MVal) : SymScalar :=
  ⟨value.type, .lit value, by cases value <;> simp [MVal.type]⟩

def ScalarDenotes (model : Model) (symbolic : SymScalar) (value : MVal) : Prop :=
  symbolic.type = value.type ∧ symbolic.term.eval model = some value

inductive FieldsDenote (model : Model) : List SymScalar → List MVal → Prop where
  | nil : FieldsDenote model [] []
  | cons : ScalarDenotes model s v → FieldsDenote model ss vs →
      FieldsDenote model (s :: ss) (v :: vs)

inductive SymValue where
  | scalar (value : SymScalar)
  | tuple (fields : Flat SymScalar)
  deriving Repr

def SymValue.type : SymValue → FlatProducts.Ty
  | .scalar v => .scalar v.type
  | .tuple fields => .tuple (fields.map SymScalar.type)

def evalFields (model : Model) : List SymScalar → Option (List MVal)
  | [] => some []
  | field :: rest => do
      let value ← field.term.eval model
      let values ← evalFields model rest
      return value :: values

def SymValue.eval (model : Model) : SymValue → Option MValue
  | .scalar value => value.term.eval model |>.map MValue.scalar
  | .tuple fields => do
      let values ← evalFields model fields.fields
      let product ← Flat.make values
      return .tuple product

inductive ProductDenotes (model : Model) : SymValue → MValue → Prop where
  | scalar : ScalarDenotes model s v → ProductDenotes model (.scalar s) (.scalar v)
  | tuple : FieldsDenote model ss.fields vs.fields → ProductDenotes model (.tuple ss) (.tuple vs)

abbrev RuntimeDenotes (model : Model) (symbolic : SymValue) (value : FlatProducts.Val) :=
  ProductDenotes model symbolic (embedValue value)

inductive EnvRep (model : Model) : List SymValue → List MValue → Prop where
  | nil : EnvRep model [] []
  | cons : ProductDenotes model s v → EnvRep model ss vs → EnvRep model (s :: ss) (v :: vs)
abbrev RuntimeEnvRep (model : Model) (symbolic : List SymValue) (values : FlatProducts.Env) :=
  EnvRep model symbolic (values.map embedValue)

theorem FieldsDenote.length (h : FieldsDenote model ss vs) : ss.length = vs.length :=
  by induction h <;> simp_all

theorem FieldsDenote.shape (h : FieldsDenote model ss vs) :
    ss.map SymScalar.type = vs.map MVal.type := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h.1, ih]

theorem FieldsDenote.eval (h : FieldsDenote model ss vs) : evalFields model ss = some vs := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [evalFields, h.2, ih]

theorem evalFields_length (h : evalFields model ss = some vs) : ss.length = vs.length := by
  induction ss generalizing vs with
  | nil => simp [evalFields] at h; subst vs; rfl
  | cons s ss ih =>
      simp only [evalFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨v, _, values, hs, hv⟩ := h
      cases hv
      simp [ih hs]

theorem evalFields_all (h : evalFields model ss = some vs)
    (hv : vs[(index : Nat)]? = some v) :
    ∃ s, ss[(index : Nat)]? = some s ∧ s.term.eval model = some v := by
  induction ss generalizing vs index with
  | nil => simp [evalFields] at h; subst vs; simp at hv
  | cons s ss ih =>
      simp only [evalFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨value, he, values, hs, hvalues⟩ := h
      cases hvalues
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
                subst v
                exact ⟨s, rfl, he⟩
      | succ index => exact ih hs hv

theorem ProductDenotes.shape (h : ProductDenotes model s v) : s.type = v.type := by
  cases h with
  | scalar h => exact congrArg FlatProducts.Ty.scalar h.1
  | tuple h => exact congrArg FlatProducts.Ty.tuple (Flat.ext h.shape)

theorem ProductDenotes.eval (h : ProductDenotes model s v) : s.eval model = some v := by
  cases h with
  | scalar h => simp [SymValue.eval, h.2]
  | tuple h => simp [SymValue.eval, h.eval]

theorem ProductDenotes.defined (h : ProductDenotes model s v) : ∃ value, s.eval model = some value :=
  ⟨v, h.eval⟩

theorem EnvRep.length (h : EnvRep model ss vs) : ss.length = vs.length :=
  by induction h <;> simp_all

theorem EnvRep.shape (h : EnvRep model ss vs) : ss.map SymValue.type = vs.map MValue.type := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h.shape, ih]

theorem EnvRep.lookup (h : EnvRep model ss vs) (hv : vs[(index : Nat)]? = some v) :
    ∃ s, ss[(index : Nat)]? = some s ∧ ProductDenotes model s v := by
  induction h generalizing index with
  | nil => simp at hv
  | @cons s v ss vs h hs ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst v
                exact ⟨s, rfl, h⟩
      | succ index => exact ih hv

theorem FieldsDenote.lookup (h : FieldsDenote model ss vs) (hv : vs[(index : Nat)]? = some v) :
    ∃ s, ss[(index : Nat)]? = some s ∧ ScalarDenotes model s v := by
  induction h generalizing index with
  | nil => simp at hv
  | @cons s v ss vs h hs ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst v
                exact ⟨s, rfl, h⟩
      | succ index => exact ih hv

def construct (fields : List SymScalar) : Option SymValue :=
  (Flat.make fields).map SymValue.tuple

theorem construct_capture (h : FieldsDenote model ss vs.fields) :
    ∃ symbolic, construct ss = some symbolic ∧ ProductDenotes model symbolic (.tuple vs) := by
  have hn : 0 < ss.length := by rw [h.length]; exact vs.nonempty
  have hb : ss.length ≤ 8 := by rw [h.length]; exact vs.bounded
  refine ⟨.tuple ⟨ss, hn, hb⟩, ?_, .tuple h⟩
  simp [construct, Flat.make, hn, hb]

def project (value : SymValue) (index : Nat) : Option SymScalar :=
  match value with
  | .scalar _ => none
  | .tuple fields => fields.fields[(index : Nat)]?

theorem project_full_base (h : ProductDenotes model s (.tuple vs))
    (hv : vs.fields[(index : Nat)]? = some v) :
    ∃ field, project s index = some field ∧ ScalarDenotes model field v := by
  cases h with
  | tuple h => exact h.lookup hv

def SymScalar.Supported (bound : Nat) (value : SymScalar) : Prop := value.term.Supported bound

def SymValue.Supported (bound : Nat) : SymValue → Prop
  | .scalar value => value.Supported bound
  | .tuple fields => ∀ field ∈ fields.fields, field.Supported bound

theorem ScalarDenotes.agree (h : ScalarDenotes left s v) (hs : s.Supported bound)
    (ha : AgreeBelow bound left right) : ScalarDenotes right s v := by
  exact ⟨h.1, (s.term.eval_agree hs ha).symm.trans h.2⟩

theorem FieldsDenote.agree (h : FieldsDenote left ss vs)
    (hs : ∀ field ∈ ss, field.Supported bound) (ha : AgreeBelow bound left right) :
    FieldsDenote right ss vs := by
  induction h with
  | nil => exact .nil
  | cons h rest ih =>
      exact .cons (h.agree (hs _ (by simp)) ha) (ih (by intro s hm; exact hs s (by simp [hm])))

theorem ProductDenotes.agree (h : ProductDenotes left s v) (hs : s.Supported bound)
    (ha : AgreeBelow bound left right) : ProductDenotes right s v := by
  cases h with
  | scalar h => exact .scalar (h.agree hs ha)
  | tuple h => exact .tuple (h.agree hs ha)

theorem EnvRep.agree (h : EnvRep left ss vs)
    (hs : ∀ value ∈ ss, value.Supported bound) (ha : AgreeBelow bound left right) :
    EnvRep right ss vs := by
  induction h with
  | nil => exact .nil
  | cons h rest ih =>
      exact .cons (h.agree (hs _ (by simp)) ha) (ih (by intro s hm; exact hs s (by simp [hm])))

def definedFields : List SymScalar → Formula
  | [] => .truth true
  | s :: ss => .and (.defined s.term) (definedFields ss)

def definedValue : SymValue → Formula
  | .scalar s => .defined s.term
  | .tuple ss => definedFields ss.fields

theorem definedFields_iff : (definedFields ss).Holds model ↔ ∃ vs, evalFields model ss = some vs := by
  induction ss with
  | nil => simp [definedFields, Formula.Holds, evalFields]
  | cons s ss ih =>
      simp only [definedFields, Formula.Holds, ih, evalFields,
        Option.bind_eq_bind, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨⟨v, hv⟩, vs, hvs⟩
        exact ⟨v :: vs, v, hv, vs, hvs, rfl⟩
      · rintro ⟨_, v, hv, vs, hvs, _⟩
        exact ⟨⟨v, hv⟩, vs, hvs⟩

theorem ProductDenotes.all_defined (h : ProductDenotes model s v) : (definedValue s).Holds model := by
  cases h with
  | scalar h => exact ⟨_, h.2⟩
  | tuple h => exact definedFields_iff.mpr ⟨_, h.eval⟩

def equalityGuard (a b : SymValue) : Formula := .and (definedValue a) (definedValue b)

def equalityFields : List SymScalar → List SymScalar → Option SymTerm
  | [], [] => some (.lit (.bool true))
  | a :: aa, b :: bb => do
      let rest ← equalityFields aa bb
      return .binary .and (.binary .eq a.term b.term) rest
  | _, _ => none

def equality (a b : SymValue) : Option SymTerm :=
  if a.type = b.type then
    match a, b with
    | .scalar a, .scalar b => some (.binary .eq a.term b.term)
    | .tuple a, .tuple b => equalityFields a.fields b.fields
    | _, _ => none
  else none

def inequality (a b : SymValue) : Option SymTerm :=
  (equality a b).map (SymTerm.unary .not)

theorem scalar_equality_eval (ha : ScalarDenotes model a va) (hb : ScalarDenotes model b vb)
    (ht : a.type = b.type) :
    (SymTerm.binary .eq a.term b.term).eval model = some (.bool (decide (va = vb))) := by
  have hv : va.type = vb.type := ha.1.symm.trans (ht.trans hb.1)
  simp [SymTerm.eval, ha.2, hb.2, VCG.mShort, VCG.mBinary, hv]

theorem eval_and (ha : a.eval model = some (.bool va)) (hb : b.eval model = some (.bool vb)) :
    (SymTerm.binary .and a b).eval model = some (.bool (va && vb)) := by
  cases va <;> simp [SymTerm.eval, ha, hb, VCG.mShort, VCG.mBinary]

theorem equalityFields_sound (ha : FieldsDenote model aa va) (hb : FieldsDenote model bb vb)
    (ht : aa.map SymScalar.type = bb.map SymScalar.type) :
    ∃ term, equalityFields aa bb = some term ∧
      term.eval model = some (.bool (decide (va = vb))) := by
  induction ha generalizing bb vb with
  | nil =>
      cases hb with
      | nil => exact ⟨_, rfl, rfl⟩
      | cons => simp at ht
  | @cons a va aa vas ha has ih =>
      cases hb with
      | nil => simp at ht
      | @cons b vb bb vbs hb hbs =>
          simp only [List.map_cons, List.cons.injEq] at ht
          obtain ⟨term, hterm, heval⟩ := ih hbs ht.2
          refine ⟨.binary .and (.binary .eq a.term b.term) term, ?_, ?_⟩
          · simp [equalityFields, hterm]
          · have he := eval_and (scalar_equality_eval ha hb ht.1) heval
            simpa only [List.cons.injEq, Bool.decide_and] using he

theorem equality_sound (ha : ProductDenotes model a va) (hb : ProductDenotes model b vb)
    (ht : a.type = b.type) :
    (equalityGuard a b).Holds model ∧
    ∃ term, equality a b = some term ∧ term.eval model = some (.bool (decide (va = vb))) := by
  refine ⟨⟨ha.all_defined, hb.all_defined⟩, ?_⟩
  cases ha with
  | @scalar a va ha =>
      cases hb with
      | @scalar b vb hb =>
          have hs := FlatProducts.Ty.scalar.inj ht
          exact ⟨.binary .eq a.term b.term, by simp [equality, ht],
            by simpa using scalar_equality_eval ha hb hs⟩
      | tuple => cases ht
  | @tuple aa va ha =>
      cases hb with
      | scalar => cases ht
      | @tuple bb vb hb =>
          have hs : aa.fields.map SymScalar.type = bb.fields.map SymScalar.type :=
            congrArg Flat.fields (FlatProducts.Ty.tuple.inj ht)
          obtain ⟨term, he, hv⟩ := equalityFields_sound ha hb hs
          refine ⟨term, by simpa [equality, ht] using he, ?_⟩
          have hx : va = vb ↔ va.fields = vb.fields := ⟨congrArg Flat.fields, Flat.ext⟩
          simpa [hx] using hv

theorem inequality_sound (ha : ProductDenotes model a va) (hb : ProductDenotes model b vb)
    (ht : a.type = b.type) :
    (equalityGuard a b).Holds model ∧
    ∃ term, inequality a b = some term ∧ term.eval model = some (.bool (decide (va ≠ vb))) := by
  obtain ⟨guard, term, he, hv⟩ := equality_sound ha hb ht
  refine ⟨guard, .unary .not term, by simp [inequality, he], ?_⟩
  simp [SymTerm.eval, hv, VCG.mUnary]

@[simp] theorem embed_scalar_injective (a b : APL.Val) : VCG.embed a = VCG.embed b ↔ a = b := by
  cases a <;> cases b <;> simp [VCG.embed, Subtype.ext_iff]

@[simp] theorem embed_fields_injective (a b : List APL.Val) :
    a.map VCG.embed = b.map VCG.embed ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp
  | cons a aa ih => cases b <;> simp [ih]

@[simp] theorem embedValue_injective (a b : FlatProducts.Val) : embedValue a = embedValue b ↔ a = b := by
  cases a with
  | scalar a => cases b <;> simp [embedValue]
  | tuple a =>
      cases b with
      | scalar => simp [embedValue]
      | tuple b =>
          simp only [embedValue, MValue.tuple.injEq, FlatProducts.Val.tuple.injEq]
          constructor
          · intro h
            apply Flat.ext
            exact (embed_fields_injective _ _).mp (congrArg Flat.fields h)
          · intro h; cases h; rfl

def mergeScalar (condition : SymTerm) (a b : SymScalar) : Option SymScalar :=
  if a.type = b.type then
    some ⟨a.type, if a.type = .unit then .lit .unit else .ite condition a.term b.term,
      by intro h; simp [h]⟩
  else none

theorem mergeScalar_eval_true (hm : mergeScalar condition a b = some result)
    (hc : condition.eval model = some (.bool true)) : result.term.eval model = a.term.eval model := by
  unfold mergeScalar at hm
  split at hm
  · cases hm
    by_cases hu : a.type = .unit
    · simp [hu, a.unit_literal hu]
    · simp [hu, hc]
  · cases hm

theorem mergeScalar_eval_false (hm : mergeScalar condition a b = some result)
    (hc : condition.eval model = some (.bool false)) : result.term.eval model = b.term.eval model := by
  unfold mergeScalar at hm
  split at hm
  next ht =>
    cases hm
    by_cases hu : a.type = .unit
    · have hb : b.type = .unit := ht.symm.trans hu
      simp [hu, b.unit_literal hb]
    · simp [hu, hc]
  · cases hm

theorem mergeScalar_shape (hm : mergeScalar condition a b = some result) :
    result.type = a.type ∧ a.type = b.type := by
  unfold mergeScalar at hm
  split at hm
  next ht => cases hm; exact ⟨rfl, ht⟩
  · cases hm

theorem mergeScalar_exists (ht : a.type = b.type) : ∃ result, mergeScalar condition a b = some result := by
  simp [mergeScalar, ht]

def mergeFields (condition : SymTerm) : List SymScalar → List SymScalar → Option (List SymScalar)
  | [], [] => some []
  | a :: aa, b :: bb => do
      let field ← mergeScalar condition a b
      let fields ← mergeFields condition aa bb
      return field :: fields
  | _, _ => none

theorem mergeFields_left (ha : FieldsDenote model aa va)
    (ht : aa.map SymScalar.type = bb.map SymScalar.type)
    (hc : condition.eval model = some (.bool true)) :
    ∃ result, mergeFields condition aa bb = some result ∧ FieldsDenote model result va := by
  induction ha generalizing bb with
  | nil => cases bb with
      | nil => exact ⟨[], rfl, .nil⟩
      | cons => simp at ht
  | @cons a va aa vas ha has ih =>
      cases bb with
      | nil => simp at ht
      | cons b bb =>
          simp only [List.map_cons, List.cons.injEq] at ht
          obtain ⟨field, hf⟩ := mergeScalar_exists (condition := condition) ht.1
          obtain ⟨fields, hfs, hrep⟩ := ih ht.2
          refine ⟨field :: fields, by simp [mergeFields, hf, hfs], .cons ?_ hrep⟩
          exact ⟨(mergeScalar_shape hf).1.trans ha.1, (mergeScalar_eval_true hf hc).trans ha.2⟩

theorem mergeFields_right (hb : FieldsDenote model bb vb)
    (ht : aa.map SymScalar.type = bb.map SymScalar.type)
    (hc : condition.eval model = some (.bool false)) :
    ∃ result, mergeFields condition aa bb = some result ∧ FieldsDenote model result vb := by
  induction hb generalizing aa with
  | nil => cases aa with
      | nil => exact ⟨[], rfl, .nil⟩
      | cons => simp at ht
  | @cons b vb bb vbs hb hbs ih =>
      cases aa with
      | nil => simp at ht
      | cons a aa =>
          simp only [List.map_cons, List.cons.injEq] at ht
          obtain ⟨field, hf⟩ := mergeScalar_exists (condition := condition) ht.1
          obtain ⟨fields, hfs, hrep⟩ := ih ht.2
          refine ⟨field :: fields, by simp [mergeFields, hf, hfs], .cons ?_ hrep⟩
          exact ⟨(mergeScalar_shape hf).1.trans (ht.1.trans hb.1), (mergeScalar_eval_false hf hc).trans hb.2⟩

def merge (condition : SymTerm) : SymValue → SymValue → Option SymValue
  | .scalar a, .scalar b => (mergeScalar condition a b).map SymValue.scalar
  | .tuple a, .tuple b => do
      let fields ← mergeFields condition a.fields b.fields
      construct fields
  | _, _ => none

theorem merge_left (ha : ProductDenotes model a va) (ht : a.type = b.type)
    (hc : condition.eval model = some (.bool true)) :
    ∃ result, merge condition a b = some result ∧ ProductDenotes model result va := by
  cases ha with
  | scalar ha =>
      cases b with
      | scalar b =>
          obtain ⟨result, hr⟩ := mergeScalar_exists (condition := condition) (FlatProducts.Ty.scalar.inj ht)
          refine ⟨.scalar result, by simp [merge, hr], .scalar ?_⟩
          exact ⟨(mergeScalar_shape hr).1.trans ha.1, (mergeScalar_eval_true hr hc).trans ha.2⟩
      | tuple => cases ht
  | tuple ha =>
      cases b with
      | scalar => cases ht
      | tuple b =>
          obtain ⟨fields, hf, hrep⟩ := mergeFields_left ha
            (congrArg Flat.fields (FlatProducts.Ty.tuple.inj ht)) hc
          obtain ⟨result, hr, hv⟩ := construct_capture hrep
          exact ⟨result, by simp [merge, hf, hr], hv⟩

theorem merge_right (hb : ProductDenotes model b vb) (ht : a.type = b.type)
    (hc : condition.eval model = some (.bool false)) :
    ∃ result, merge condition a b = some result ∧ ProductDenotes model result vb := by
  cases hb with
  | scalar hb =>
      cases a with
      | scalar a =>
          have hs := FlatProducts.Ty.scalar.inj ht
          obtain ⟨result, hr⟩ := mergeScalar_exists (condition := condition) hs
          refine ⟨.scalar result, by simp [merge, hr], .scalar ?_⟩
          exact ⟨(mergeScalar_shape hr).1.trans (hs.trans hb.1), (mergeScalar_eval_false hr hc).trans hb.2⟩
      | tuple => cases ht
  | tuple hb =>
      cases a with
      | scalar => cases ht
      | tuple a =>
          obtain ⟨fields, hf, hrep⟩ := mergeFields_right hb
            (congrArg Flat.fields (FlatProducts.Ty.tuple.inj ht)) hc
          obtain ⟨result, hr, hv⟩ := construct_capture hrep
          exact ⟨result, by simp [merge, hf, hr], hv⟩

theorem merge_selected (hv : ProductDenotes model (if selected then a else b) value)
    (ht : a.type = b.type) (hc : condition.eval model = some (.bool selected)) :
    ∃ result, merge condition a b = some result ∧ ProductDenotes model result value := by
  cases selected with
  | false => exact merge_right hv ht hc
  | true => exact merge_left hv ht hc

theorem runtime_equality_sound (ha : RuntimeDenotes model a va) (hb : RuntimeDenotes model b vb)
    (ht : a.type = b.type) :
    (equalityGuard a b).Holds model ∧
    ∃ term, equality a b = some term ∧ term.eval model = some (.bool (decide (va = vb))) := by
  simpa only [embedValue_injective] using equality_sound ha hb ht

theorem runtime_inequality_sound (ha : RuntimeDenotes model a va) (hb : RuntimeDenotes model b vb)
    (ht : a.type = b.type) :
    (equalityGuard a b).Holds model ∧
    ∃ term, inequality a b = some term ∧ term.eval model = some (.bool (decide (va ≠ vb))) := by
  simpa only [ne_eq, embedValue_injective] using inequality_sound ha hb ht

def mergeEnv (condition : SymTerm) : List SymValue → List SymValue → Option (List SymValue)
  | [], [] => some []
  | a :: aa, b :: bb => do
      let value ← merge condition a b
      let values ← mergeEnv condition aa bb
      return value :: values
  | _, _ => none

theorem mergeEnv_left (ha : EnvRep model aa va)
    (ht : aa.map SymValue.type = bb.map SymValue.type)
    (hc : condition.eval model = some (.bool true)) :
    ∃ result, mergeEnv condition aa bb = some result ∧ EnvRep model result va := by
  induction ha generalizing bb with
  | nil => cases bb with
      | nil => exact ⟨[], rfl, .nil⟩
      | cons => simp at ht
  | @cons a va aa vas ha has ih =>
      cases bb with
      | nil => simp at ht
      | cons b bb =>
          simp only [List.map_cons, List.cons.injEq] at ht
          obtain ⟨value, hv, hvalue⟩ := merge_left ha ht.1 hc
          obtain ⟨values, hvs, hvalues⟩ := ih ht.2
          exact ⟨value :: values, by simp [mergeEnv, hv, hvs], .cons hvalue hvalues⟩

theorem mergeEnv_right (hb : EnvRep model bb vb)
    (ht : aa.map SymValue.type = bb.map SymValue.type)
    (hc : condition.eval model = some (.bool false)) :
    ∃ result, mergeEnv condition aa bb = some result ∧ EnvRep model result vb := by
  induction hb generalizing aa with
  | nil => cases aa with
      | nil => exact ⟨[], rfl, .nil⟩
      | cons => simp at ht
  | @cons b vb bb vbs hb hbs ih =>
      cases aa with
      | nil => simp at ht
      | cons a aa =>
          simp only [List.map_cons, List.cons.injEq] at ht
          obtain ⟨value, hv, hvalue⟩ := merge_right hb ht.1 hc
          obtain ⟨values, hvs, hvalues⟩ := ih ht.2
          exact ⟨value :: values, by simp [mergeEnv, hv, hvs], .cons hvalue hvalues⟩

theorem mergeEnv_selected (hv : EnvRep model (if selected then aa else bb) values)
    (ht : aa.map SymValue.type = bb.map SymValue.type)
    (hc : condition.eval model = some (.bool selected)) :
    ∃ result, mergeEnv condition aa bb = some result ∧ EnvRep model result values := by
  cases selected with
  | false => exact mergeEnv_right hv ht hc
  | true => exact mergeEnv_left hv ht hc

theorem EnvRep.replace (h : EnvRep model ss vs) (hv : ProductDenotes model s v) (index : Nat) :
    EnvRep model (ss.set index s) (vs.set index v) := by
  induction h generalizing index with
  | nil => exact .nil
  | cons h rest ih =>
      cases index with
      | zero => exact .cons hv rest
      | succ index => exact .cons h (ih index)

theorem EnvRep.reverse (h : EnvRep model ss vs) : EnvRep model ss.reverse vs.reverse := by
  have append : ∀ {a b c d}, EnvRep model a b → EnvRep model c d → EnvRep model (a ++ c) (b ++ d) := by
    intro a b c d hab hcd
    induction hab with
    | nil => exact hcd
    | cons h rest ih => exact .cons h ih
  induction h with
  | nil => exact .nil
  | cons h rest ih => simpa using append ih (.cons h .nil)

def MValue.Representable : MValue → Prop
  | .scalar value => value.Representable
  | .tuple fields => ∀ value ∈ fields.fields, value.Representable

theorem scalar_runtime_lift (h : value.Representable) : ∃ runtime, VCG.embed runtime = value := by
  cases value with
  | int n => exact ⟨.int ⟨n, h⟩, rfl⟩
  | bool b => exact ⟨.bool b, rfl⟩
  | unit => exact ⟨.unit, rfl⟩

theorem fields_runtime_lift {values : List MVal} (h : ∀ value ∈ values, value.Representable) :
    ∃ runtime : List APL.Val, runtime.map VCG.embed = values := by
  induction values with
  | nil => exact ⟨[], rfl⟩
  | cons value values ih =>
      obtain ⟨runtime, hv⟩ := scalar_runtime_lift (h value (by simp))
      obtain ⟨runtimes, hvs⟩ := ih (by intro v hm; exact h v (by simp [hm]))
      exact ⟨runtime :: runtimes, by simp [hv, hvs]⟩

theorem MValue.runtime_lift (h : value.Representable) : ∃ runtime, embedValue runtime = value := by
  cases value with
  | scalar value =>
      obtain ⟨runtime, hr⟩ := scalar_runtime_lift h
      exact ⟨.scalar runtime, congrArg MValue.scalar hr⟩
  | tuple values =>
      obtain ⟨runtime, hr⟩ := fields_runtime_lift h
      have hl : runtime.length = values.fields.length := by simpa using congrArg List.length hr
      let fields : Flat APL.Val := ⟨runtime, by rw [hl]; exact values.nonempty,
        by rw [hl]; exact values.bounded⟩
      exact ⟨.tuple fields, congrArg MValue.tuple (Flat.ext hr)⟩

theorem runtime_lift_typed (hr : value.Representable) (ht : value.type = type) :
    ∃ runtime, runtime.type = type ∧ embedValue runtime = value := by
  obtain ⟨runtime, hv⟩ := MValue.runtime_lift hr
  exact ⟨runtime, (embedValue_type runtime).symm.trans ((congrArg MValue.type hv).trans ht), hv⟩

theorem embedValue_representable (runtime : FlatProducts.Val) : (embedValue runtime).Representable := by
  have scalar (value : APL.Val) : (VCG.embed value).Representable := by
    cases value with
    | int n => exact n.property
    | bool => trivial
    | unit => trivial
  cases runtime with
  | scalar value => exact scalar value
  | tuple values =>
      intro value hv
      obtain ⟨runtime, _, rfl⟩ := List.mem_map.mp hv
      exact scalar runtime

theorem flatProducts_equality (ht : a.type = b.type) :
    FlatProducts.binary .eq a b = .value (.scalar (.bool (decide (a = b)))) := by
  cases a with
  | scalar a =>
      cases b with
      | scalar b =>
          have hs := FlatProducts.Ty.scalar.inj ht
          simp [FlatProducts.binary, APL.binary, hs, FlatProducts.embedResult]
      | tuple => cases ht
  | tuple a =>
      cases b with
      | scalar => cases ht
      | tuple b =>
          have hs := FlatProducts.Ty.tuple.inj ht
          have hx : a = b ↔ a.fields = b.fields := ⟨congrArg Flat.fields, Flat.ext⟩
          simp [FlatProducts.binary, hs, hx]

theorem flatProducts_inequality (ht : a.type = b.type) :
    FlatProducts.binary .ne a b = .value (.scalar (.bool (decide (a ≠ b)))) := by
  cases a with
  | scalar a =>
      cases b with
      | scalar b =>
          have hs := FlatProducts.Ty.scalar.inj ht
          have he : (a != b) = decide (a ≠ b) := by
            apply Bool.eq_iff_iff.mpr
            simp [bne_iff_ne]
          simp [FlatProducts.binary, APL.binary, hs, FlatProducts.embedResult, he]
      | tuple => cases ht
  | tuple a =>
      cases b with
      | scalar => cases ht
      | tuple b =>
          have hs := FlatProducts.Ty.tuple.inj ht
          have hx : a = b ↔ a.fields = b.fields := ⟨congrArg Flat.fields, Flat.ext⟩
          simp [FlatProducts.binary, hs, hx]

end APL.ProductLogic
