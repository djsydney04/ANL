import APL.ProductAnnotations
import APL.ProductFlowSupport

namespace APL.ProductAnnotations
open ProductLogic
open VCG (MVal Model)

def mathUnary (op : UOp) : MValue → Option MValue
  | .scalar value => (VCG.mUnary op value).map MValue.scalar
  | .tuple _ => none

def mathShort (op : BOp) : MValue → Bool
  | .scalar value => VCG.mShort op value
  | .tuple _ => false

def mathBinary (op : BOp) (a b : MValue) : Option MValue :=
  match a, b with
  | .scalar a, .scalar b => (VCG.mBinary op a b).map MValue.scalar
  | .tuple a, .tuple b =>
      if a.map MVal.type = b.map MVal.type then
        match op with
        | .eq => some (.scalar (.bool (decide (a.fields = b.fields))))
        | .ne => some (.scalar (.bool (!decide (a.fields = b.fields))))
        | _ => none
      else none
  | _, _ => none

def mathScalar : MValue → Option MVal
  | .scalar value => some value
  | .tuple _ => none

def mathConstruct (values : List MValue) : Option MValue := do
  let fields ← values.mapM mathScalar
  let product ← FlatProducts.Flat.make fields
  return .tuple product

def mathProject (base : MValue) (index : Nat) : Option MValue :=
  match base with
  | .scalar _ => none
  | .tuple fields => (fields.fields[index]?).map MValue.scalar

def Spec.eval (params : List MValue) (result : Option MValue) (locals : List MValue) :
    Spec → Option MValue
  | .lit value => some (.scalar value)
  | .param index => params[index]?
  | .result => result
  | .local index => locals[index]?
  | .unary op operand => do mathUnary op (← operand.eval params result locals)
  | .binary op left right => do
      let a ← left.eval params result locals
      if mathShort op a then some a else mathBinary op a (← right.eval params result locals)
  | .tuple fields => do mathConstruct (← fields.mapM (Spec.eval params result locals))
  | .project base index => do mathProject (← base.eval params result locals) index

structure Instantiated where
  value : SymValue
  defined : Formula
  deriving Repr

def Instantiated.Denotes (model : Model) (symbolic : Instantiated) (value : MValue) : Prop :=
  symbolic.defined.Holds model ∧ ProductDenotes model symbolic.value value

def resultScalar : BOp → APL.Ty
  | .add | .sub | .mul | .div | .rem => .i64
  | _ => .bool

def unaryScalar (op : UOp) (term : SymTerm) : SymScalar :=
  ⟨op.output, .unary op term, by cases op <;> simp [UOp.output]⟩

def binaryScalar (op : BOp) (a b : SymTerm) : SymScalar :=
  ⟨resultScalar op, .binary op a b, by cases op <;> simp [resultScalar]⟩

def boolScalar (term : SymTerm) : SymScalar := ⟨.bool, term, by simp⟩

def shortGuard (op : BOp) (value : SymTerm) : Formula :=
  match op with
  | .and => .holds (.unary .not value)
  | .or => .holds value
  | _ => .truth false

def instantiateUnary (op : UOp) (operand : Instantiated) : Option Instantiated :=
  match operand.value with
  | .scalar value =>
      if value.type = op.input then
        some ⟨.scalar (unaryScalar op value.term),
          .and operand.defined (.defined (.unary op value.term))⟩
      else none
  | .tuple _ => none

def instantiateBinary (op : BOp) (left right : Instantiated) : Option Instantiated := do
  let _ ← FlatProducts.binaryType op left.value.type right.value.type
  match left.value, right.value with
  | .scalar a, .scalar b =>
      return ⟨.scalar (binaryScalar op a.term b.term),
        .and left.defined (.and (.imp (.not (shortGuard op a.term)) right.defined)
          (.defined (.binary op a.term b.term)))⟩
  | .tuple a, .tuple b =>
      let term ← (if op = .ne then inequality (.tuple a) (.tuple b) else equality (.tuple a) (.tuple b))
      return ⟨.scalar (boolScalar term), .and left.defined right.defined⟩
  | _, _ => none

def instantiatedScalar (value : Instantiated) : Option SymScalar :=
  match value.value with
  | .scalar scalar => some scalar
  | .tuple _ => none

def allDefined : List Instantiated → Formula
  | [] => .truth true
  | value :: values => .and value.defined (allDefined values)

def instantiateTuple (values : List Instantiated) : Option Instantiated := do
  let fields ← values.mapM instantiatedScalar
  let product ← construct fields
  return ⟨product, allDefined values⟩

def instantiateProject (base : Instantiated) (index : Nat) : Option Instantiated := do
  let field ← project base.value index
  return ⟨.scalar field, base.defined⟩

def Spec.instantiate (params : List SymValue) (result : Option SymValue) (locals : List SymValue) :
    Spec → Option Instantiated
  | .lit value => some ⟨.scalar (.literal value), .truth true⟩
  | .param index => (params[index]?).map fun value => ⟨value, .truth true⟩
  | .result => result.map fun value => ⟨value, .truth true⟩
  | .local index => (locals[index]?).map fun value => ⟨value, .truth true⟩
  | .unary op operand => do instantiateUnary op (← operand.instantiate params result locals)
  | .binary op left right => do
      instantiateBinary op (← left.instantiate params result locals) (← right.instantiate params result locals)
  | .tuple fields => do instantiateTuple (← fields.mapM (Spec.instantiate params result locals))
  | .project base index => do instantiateProject (← base.instantiate params result locals) index

def ResultRep (model : Model) : Option SymValue → Option MValue → Prop
  | none, none => True
  | some symbolic, some value => ProductDenotes model symbolic value
  | _, _ => False

theorem short_guard_sound (h : ScalarDenotes model symbolic value) :
    (shortGuard op symbolic.term).Holds model ↔ VCG.mShort op value = true := by
  cases op <;> cases value <;>
    simp [shortGuard, Formula.Holds, SymTerm.eval, h.2, VCG.mShort, VCG.mUnary]
  all_goals cases ‹Bool› <;> rfl

theorem math_unary_type (h : VCG.mUnary op a = some b) : b.type = op.output := by
  cases op <;> cases a <;> simp [VCG.mUnary] at h <;> cases h <;> rfl

theorem math_binary_type (h : VCG.mBinary op a b = some value) : value.type = resultScalar op := by
  cases op <;> cases a <;> cases b <;> simp [VCG.mBinary, MVal.type] at h
  all_goals first | cases h; rfl | rcases h with ⟨_, rfl⟩; rfl

theorem instantiate_unary_sound (hg : instantiateUnary op input = some output)
    (hinput : input.Denotes model value) (hdefined : output.defined.Holds model) :
    ∃ actual, mathUnary op value = some actual ∧ output.Denotes model actual := by
  obtain ⟨hin, hval⟩ := hinput
  cases input with
  | mk symbol defined =>
    cases symbol with
    | tuple fields => simp [instantiateUnary] at hg
    | scalar symbol =>
      simp only [instantiateUnary] at hg
      split at hg
      next ht =>
        cases hg
        cases hval with
        | @scalar _ value hv =>
          obtain ⟨result, hr⟩ := hdefined.2
          have hr : VCG.mUnary op value = some result := by simpa [SymTerm.eval, hv.2] using hr
          exact ⟨.scalar result, by simp [mathUnary, hr], hdefined,
            .scalar ⟨(math_unary_type hr).symm, by simp [unaryScalar, SymTerm.eval, hv.2, hr]⟩⟩
      · contradiction

def Instantiated.Agrees (model : Model) (symbolic : Instantiated) (semantic : Option MValue) : Prop :=
  (symbolic.defined.Holds model → ∃ value, semantic = some value ∧
    ProductDenotes model symbolic.value value) ∧
  (∀ value, semantic = some value → symbolic.Denotes model value)

theorem math_equality (ht : a.type = b.type) :
    mathBinary .eq a b = some (.scalar (.bool (decide (a = b)))) := by
  cases a with
  | scalar a =>
    cases b with
    | scalar b =>
      have h := FlatProducts.Ty.scalar.inj ht
      simp [mathBinary, VCG.mBinary, h]
    | tuple b => cases ht
  | tuple a =>
    cases b with
    | scalar b => cases ht
    | tuple b =>
      have h := FlatProducts.Ty.tuple.inj ht
      have he : a = b ↔ a.fields = b.fields := ⟨congrArg FlatProducts.Flat.fields, FlatProducts.Flat.ext⟩
      simp [mathBinary, h, he]

theorem math_inequality (ht : a.type = b.type) :
    mathBinary .ne a b = some (.scalar (.bool (decide (a ≠ b)))) := by
  cases a with
  | scalar a =>
    cases b with
    | scalar b =>
      have h := FlatProducts.Ty.scalar.inj ht
      cases a <;> cases b <;> simp_all [mathBinary, VCG.mBinary, MVal.type, bne, Bool.beq_eq_decide_eq]
    | tuple b => cases ht
  | tuple a =>
    cases b with
    | scalar b => cases ht
    | tuple b =>
      have h := FlatProducts.Ty.tuple.inj ht
      have he : a = b ↔ a.fields = b.fields := ⟨congrArg FlatProducts.Flat.fields, FlatProducts.Flat.ext⟩
      simp [mathBinary, h, he]

theorem math_short_type (h : VCG.mShort op value = true) : value.type = resultScalar op := by
  cases op <;> cases value <;> simp [VCG.mShort] at h
  all_goals rfl

theorem instantiate_unary_complete (hg : instantiateUnary op input = some output)
    (hinput : input.Denotes model value) (he : mathUnary op value = some actual) :
    output.Denotes model actual := by
  obtain ⟨hin, hv⟩ := hinput
  cases input with
  | mk symbol defined =>
    cases symbol with
    | tuple fields => simp [instantiateUnary] at hg
    | scalar symbol =>
      simp only [instantiateUnary] at hg
      split at hg
      next ht =>
        cases hg
        cases hv with
        | scalar hv =>
          simp only [mathUnary, Option.map_eq_some_iff] at he
          obtain ⟨result, hr, rfl⟩ := he
          have heval : (SymTerm.unary op symbol.term).eval model = some result := by
            simp [SymTerm.eval, hv.2, hr]
          exact ⟨⟨hin, result, heval⟩, .scalar ⟨(math_unary_type hr).symm, heval⟩⟩
      · contradiction

theorem instantiate_unary_agrees (hg : instantiateUnary op input = some output)
    (hi : input.Agrees model semantic) :
    output.Agrees model (semantic.bind (mathUnary op)) := by
  constructor
  · intro hd
    have hid : input.defined.Holds model := by
      cases input with
      | mk symbol defined =>
        cases symbol <;> simp only [instantiateUnary] at hg
        · split at hg
          · cases hg; exact hd.1
          · contradiction
        · contradiction
    obtain ⟨value, hv, hr⟩ := hi.1 hid
    obtain ⟨actual, he, ha⟩ := instantiate_unary_sound hg ⟨hid, hr⟩ hd
    exact ⟨actual, by simp [hv, he], ha.2⟩
  · intro actual he
    obtain ⟨value, hv, he⟩ := Option.bind_eq_some_iff.mp he
    exact instantiate_unary_complete hg (hi.2 value hv) he

theorem scalar_binary_agrees (left right : SymScalar)
    (hl : (Instantiated.mk (.scalar left) leftDefined).Agrees model a)
    (hr : (Instantiated.mk (.scalar right) rightDefined).Agrees model b) :
    (Instantiated.mk (.scalar (binaryScalar op left.term right.term))
      (.and leftDefined (.and (.imp (.not (shortGuard op left.term)) rightDefined)
        (.defined (.binary op left.term right.term))))).Agrees model
      (a.bind fun value => if mathShort op value then some value else b.bind (mathBinary op value)) := by
  constructor
  · rintro ⟨hd, hright, he⟩
    obtain ⟨value, hv, hrep⟩ := hl.1 hd
    cases hrep with
    | @scalar _ value hrep =>
      cases hs : VCG.mShort op value with
      | true =>
        have heval : (SymTerm.binary op left.term right.term).eval model = some value := by
          simp [SymTerm.eval, hrep.2, hs]
        exact ⟨.scalar value, by simp [hv, mathShort, hs],
          .scalar ⟨(math_short_type hs).symm, heval⟩⟩
      | false =>
        have hnot : ¬ (shortGuard op left.term).Holds model := by
          intro h
          have := (short_guard_sound hrep).mp h
          rw [hs] at this
          contradiction
        obtain ⟨other, hb, hbRep⟩ := hr.1 (hright hnot)
        cases hbRep with
        | @scalar _ other hbRep =>
          obtain ⟨actual, ha⟩ := he
          have hop : VCG.mBinary op value other = some actual := by
            simpa [SymTerm.eval, hrep.2, hs, hbRep.2] using ha
          exact ⟨.scalar actual, by simp [hv, hb, mathShort, hs, mathBinary, hop],
            .scalar ⟨(math_binary_type hop).symm, ha⟩⟩
  · intro actual he
    obtain ⟨value, hv, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨hd, hrep⟩ := hl.2 value hv
    cases hrep with
    | @scalar _ value hrep =>
      cases hs : VCG.mShort op value with
      | true =>
        simp only [mathShort, hs, ↓reduceIte, Option.some.injEq] at he
        subst actual
        have heval : (SymTerm.binary op left.term right.term).eval model = some value := by
          simp [SymTerm.eval, hrep.2, hs]
        refine ⟨⟨hd, ?_, value, heval⟩, .scalar ⟨(math_short_type hs).symm, heval⟩⟩
        intro hnot
        exact False.elim (hnot ((short_guard_sound hrep).mpr hs))
      | false =>
        simp only [mathShort, hs, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at he
        obtain ⟨other, hb, he⟩ := he
        obtain ⟨hbd, hbrep⟩ := hr.2 other hb
        cases hbrep with
        | @scalar _ other hbrep =>
          simp only [mathBinary, Option.map_eq_some_iff] at he
          obtain ⟨result, hop, rfl⟩ := he
          have heval : (SymTerm.binary op left.term right.term).eval model = some result := by
            simp [SymTerm.eval, hrep.2, hbrep.2, hs, hop]
          exact ⟨⟨hd, fun _ => hbd, result, heval⟩,
            .scalar ⟨(math_binary_type hop).symm, heval⟩⟩

theorem equality_instantiated (hop : op = .eq ∨ op = .ne) (ht : left.type = right.type)
    (hterm : (if op = .ne then inequality left right else equality left right) = some term)
    (hl : ProductDenotes model left a) (hr : ProductDenotes model right b) :
    ∃ value, mathBinary op a b = some value ∧
      ProductDenotes model (.scalar (boolScalar term)) value := by
  have shape : a.type = b.type := hl.shape.symm.trans (ht.trans hr.shape)
  rcases hop with rfl | rfl
  · obtain ⟨_, actual, hg, he⟩ := equality_sound hl hr ht
    change equality left right = some term at hterm
    rw [hg] at hterm
    cases hterm
    exact ⟨.scalar (.bool (decide (a = b))), math_equality shape, .scalar ⟨rfl, he⟩⟩
  · obtain ⟨_, actual, hg, he⟩ := inequality_sound hl hr ht
    change inequality left right = some term at hterm
    rw [hg] at hterm
    cases hterm
    exact ⟨.scalar (.bool (decide (a ≠ b))), math_inequality shape, .scalar ⟨rfl, he⟩⟩

theorem instantiate_binary_agrees (hg : instantiateBinary op left right = some output)
    (hl : left.Agrees model a) (hr : right.Agrees model b) :
    output.Agrees model
      (a.bind fun value => if mathShort op value then some value else b.bind (mathBinary op value)) := by
  cases left with
  | mk left dl =>
    cases right with
    | mk right dr =>
      cases left with
      | scalar left =>
        cases right with
        | scalar right =>
          simp only [instantiateBinary, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
          obtain ⟨type, _, heq⟩ := hg
          cases heq
          exact scalar_binary_agrees left right hl hr
        | tuple right => simp [instantiateBinary, SymValue.type, FlatProducts.binaryType] at hg
      | tuple left =>
        cases right with
        | scalar right => simp [instantiateBinary, SymValue.type, FlatProducts.binaryType] at hg
        | tuple right =>
          simp only [instantiateBinary, SymValue.type, FlatProducts.binaryType] at hg
          split at hg
          next ht =>
            change ((if op = .ne then inequality (.tuple left) (.tuple right)
              else equality (.tuple left) (.tuple right)).bind fun term =>
                some ⟨.scalar (boolScalar term), .and dl dr⟩) = some output at hg
            simp only [Option.bind_eq_some_iff] at hg
            obtain ⟨term, hterm, heq⟩ := hg
            cases heq
            have shape : (SymValue.tuple left).type = (SymValue.tuple right).type := congrArg FlatProducts.Ty.tuple ht.2
            constructor
            · rintro ⟨hld, hrd⟩
              obtain ⟨va, hva, ha⟩ := hl.1 hld
              obtain ⟨vb, hvb, hb⟩ := hr.1 hrd
              obtain ⟨value, heval, hrep⟩ := equality_instantiated ht.1 shape hterm ha hb
              have hshort : mathShort op va = false := by cases ha; rfl
              exact ⟨value, by simp [hva, hvb, hshort, heval], hrep⟩
            · intro actual he
              obtain ⟨va, hva, he⟩ := Option.bind_eq_some_iff.mp he
              obtain ⟨hld, ha⟩ := hl.2 va hva
              have hshort : mathShort op va = false := by cases ha; rfl
              simp only [hshort, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at he
              obtain ⟨vb, hvb, he⟩ := he
              obtain ⟨hrd, hb⟩ := hr.2 vb hvb
              obtain ⟨value, heval, hrep⟩ := equality_instantiated ht.1 shape hterm ha hb
              rw [he] at heval
              cases heval
              exact ⟨⟨hld, hrd⟩, hrep⟩
          · simp at hg

inductive FieldsAgree (model : Model) (eval : α → Option MValue) : List Instantiated → List α → Prop where
  | nil : FieldsAgree model eval [] []
  | cons : symbolic.Agrees model (eval source) → FieldsAgree model eval symbols sources →
      FieldsAgree model eval (symbolic :: symbols) (source :: sources)

theorem lists_agree (eval : α → Option MValue)
    (h : FieldsAgree model eval symbols sources) :
    ((allDefined symbols).Holds model → ∃ values, sources.mapM eval = some values ∧
      EnvRep model (symbols.map Instantiated.value) values) ∧
    (∀ values, sources.mapM eval = some values →
      (allDefined symbols).Holds model ∧ EnvRep model (symbols.map Instantiated.value) values) := by
  induction h with
  | nil =>
    constructor
    · intro _; exact ⟨[], rfl, .nil⟩
    · intro values hv; cases hv; exact ⟨rfl, .nil⟩
  | @cons symbolic source symbols sources h hs ih =>
    constructor
    · rintro ⟨hd, hds⟩
      obtain ⟨value, hv, hr⟩ := h.1 hd
      obtain ⟨values, hvs, hrs⟩ := ih.1 hds
      exact ⟨value :: values, by simp [List.mapM_cons, hv, hvs], .cons hr hrs⟩
    · intro values he
      simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at he
      obtain ⟨value, hv, rest, hr, he⟩ := he
      cases he
      obtain ⟨hd, hp⟩ := h.2 value hv
      obtain ⟨hds, hps⟩ := ih.2 rest hr
      exact ⟨⟨hd, hds⟩, .cons hp hps⟩

theorem instantiated_fields_sound {symbols : List Instantiated} (hg : symbols.mapM instantiatedScalar = some fields)
    (hr : EnvRep model (symbols.map Instantiated.value) values) :
    ∃ scalars, values = scalars.map MValue.scalar ∧ FieldsDenote model fields scalars := by
  induction symbols generalizing fields values with
  | nil => cases hr; cases hg; exact ⟨[], rfl, .nil⟩
  | cons symbol symbols ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨field, hf, rest, hs, he⟩ := hg
    cases he
    cases symbol with
    | mk value defined =>
      cases value with
      | tuple fields => simp [instantiatedScalar] at hf
      | scalar scalar =>
        simp only [instantiatedScalar, Option.some.injEq] at hf
        subst field
        cases hr with
        | cons hv hr =>
          cases hv with
          | scalar hv =>
            obtain ⟨scalars, rfl, hfields⟩ := ih hs hr
            exact ⟨_ :: scalars, rfl, .cons hv hfields⟩

theorem math_scalars_map (values : List MVal) :
    (values.map MValue.scalar).mapM mathScalar = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [mathScalar, List.mapM_cons, ih]

theorem construct_instantiated (hg : construct fields = some symbol)
    (hr : FieldsDenote model fields values) :
    ∃ actual, mathConstruct (values.map MValue.scalar) = some actual ∧
      ProductDenotes model symbol actual := by
  simp only [construct, Option.map_eq_some_iff] at hg
  obtain ⟨product, hp, rfl⟩ := hg
  have hf := FlatProducts.make_fields hp
  have hl := hr.length
  let actual : FlatProducts.Flat MVal := ⟨values,
    by rw [← hl, ← hf]; exact product.nonempty,
    by rw [← hl, ← hf]; exact product.bounded⟩
  refine ⟨.tuple actual, ?_, ?_⟩
  · simp only [mathConstruct, math_scalars_map, bind, Option.bind_some, Option.pure_def]
    change (FlatProducts.Flat.make actual.fields).bind _ = _
    simp
  · exact .tuple (hf ▸ hr)

theorem instantiate_tuple_agrees (eval : α → Option MValue)
    (hg : instantiateTuple symbols = some output)
    (h : FieldsAgree model eval symbols sources) :
    output.Agrees model ((sources.mapM eval).bind mathConstruct) := by
  simp only [instantiateTuple, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨fields, hfields, product, hp, heq⟩ := hg
  cases heq
  have ha := lists_agree eval h
  constructor
  · intro hd
    obtain ⟨values, hv, hr⟩ := ha.1 hd
    obtain ⟨scalars, rfl, hrep⟩ := instantiated_fields_sound hfields hr
    obtain ⟨actual, he, hrep⟩ := construct_instantiated hp hrep
    exact ⟨actual, by simp [hv, he], hrep⟩
  · intro actual he
    obtain ⟨values, hv, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨hd, hr⟩ := ha.2 values hv
    obtain ⟨scalars, rfl, hrep⟩ := instantiated_fields_sound hfields hr
    obtain ⟨expected, he', hrep⟩ := construct_instantiated hp hrep
    rw [he] at he'
    cases he'
    exact ⟨hd, hrep⟩

theorem fields_lookup_symbol (h : FieldsDenote model symbols values)
    (hs : symbols[(index : Nat)]? = some symbol) :
    ∃ value, values[index]? = some value ∧ ScalarDenotes model symbol value := by
  induction h generalizing index with
  | nil => simp at hs
  | @cons symbol value symbols values h hs' ih =>
    cases index with
    | zero => cases hs; exact ⟨value, rfl, h⟩
    | succ index => exact ih hs

theorem project_instantiated (hg : project symbol index = some field)
    (hr : ProductDenotes model symbol value) :
    ∃ actual, mathProject value index = some actual ∧
      ProductDenotes model (.scalar field) actual := by
  cases hr with
  | scalar hr => simp [project] at hg
  | tuple hr =>
    obtain ⟨actual, ha, hrep⟩ := fields_lookup_symbol hr hg
    exact ⟨.scalar actual, by simp [mathProject, ha], .scalar hrep⟩

theorem instantiate_project_agrees (hg : instantiateProject input index = some output)
    (h : input.Agrees model semantic) :
    output.Agrees model (semantic.bind (fun value => mathProject value index)) := by
  simp only [instantiateProject, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨field, hf, he⟩ := hg
  cases he
  constructor
  · intro hd
    obtain ⟨value, hv, hr⟩ := h.1 hd
    obtain ⟨actual, he, hr⟩ := project_instantiated hf hr
    exact ⟨actual, by simp [hv, he], hr⟩
  · intro actual he
    obtain ⟨value, hv, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨hd, hr⟩ := h.2 value hv
    obtain ⟨expected, he', hr⟩ := project_instantiated hf hr
    rw [he] at he'
    cases he'
    exact ⟨hd, hr⟩

theorem env_lookup_symbol (h : EnvRep model symbols values)
    (hs : symbols[(index : Nat)]? = some symbol) :
    ∃ value, values[index]? = some value ∧ ProductDenotes model symbol value := by
  induction h generalizing index with
  | nil => simp at hs
  | @cons symbol value symbols values h hs' ih =>
    cases index with
    | zero => cases hs; exact ⟨value, rfl, h⟩
    | succ index => exact ih hs

theorem constant_agrees (h : ProductDenotes model symbolic value) :
    (Instantiated.mk symbolic (.truth true)).Agrees model (some value) := by
  constructor
  · intro _; exact ⟨value, rfl, h⟩
  · intro actual he; cases he; exact ⟨rfl, h⟩

theorem lookup_agrees (h : EnvRep model symbols values)
    (hs : symbols[(index : Nat)]? = some symbol) :
    (Instantiated.mk symbol (.truth true)).Agrees model values[index]? := by
  obtain ⟨value, hv, hr⟩ := env_lookup_symbol h hs
  rw [hv]
  exact constant_agrees hr

theorem Spec.instantiate_sound {spec : Spec} {result : Option MValue}
    (hg : spec.instantiate symbolicParams symbolicResult symbolicLocals = some output)
    (hp : EnvRep model symbolicParams params)
    (hr : ResultRep model symbolicResult result)
    (hl : EnvRep model symbolicLocals locals) :
    output.Agrees model (spec.eval params result locals) := by
  induction spec using Spec.rec
    (motive_2 := fun specs => ∀ outputs,
      specs.mapM (Spec.instantiate symbolicParams symbolicResult symbolicLocals) = some outputs →
      FieldsAgree model (Spec.eval params result locals) outputs specs)
    generalizing output with
  | lit value =>
    simp only [Spec.instantiate, Option.some.injEq] at hg
    subst output
    simp only [Spec.eval]
    exact constant_agrees (.scalar ⟨rfl, rfl⟩)
  | param index =>
    simp only [Spec.eval]
    simp only [Spec.instantiate, Option.map_eq_some_iff] at hg
    obtain ⟨symbol, hs, rfl⟩ := hg
    exact lookup_agrees hp hs
  | result =>
    simp only [Spec.eval]
    cases symbolicResult with
    | none => simp [Spec.instantiate] at hg
    | some symbol =>
      simp only [Spec.instantiate, Option.map_some, Option.some.injEq] at hg
      subst output
      cases result with
      | none => contradiction
      | some value => exact constant_agrees hr
  | «local» index =>
    simp only [Spec.eval]
    simp only [Spec.instantiate, Option.map_eq_some_iff] at hg
    obtain ⟨symbol, hs, rfl⟩ := hg
    exact lookup_agrees hl hs
  | unary op operand ih =>
    simp only [Spec.eval]
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨input, hi, hg⟩ := hg
    exact instantiate_unary_agrees hg (ih hi)
  | binary op left right iha ihb =>
    simp only [Spec.eval]
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨a, ha, b, hb, hg⟩ := hg
    exact instantiate_binary_agrees hg (iha ha) (ihb hb)
  | tuple fields ih =>
    simp only [Spec.eval]
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨fields, hf, hg⟩ := hg
    exact instantiate_tuple_agrees _ hg (ih fields hf)
  | project base index ih =>
    simp only [Spec.eval]
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨base, hb, hg⟩ := hg
    exact instantiate_project_agrees hg (ih hb)
  | nil outputs hg => cases hg; exact .nil
  | cons spec specs ih ihs outputs hg =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨output, ho, outputs, hos, heq⟩ := hg
    cases heq
    exact .cons (ih ho) (ihs outputs hos)

theorem Spec.instantiate_defined {spec : Spec} {result : Option MValue}
    (hg : spec.instantiate symbolicParams symbolicResult symbolicLocals = some output)
    (hp : EnvRep model symbolicParams params) (hr : ResultRep model symbolicResult result)
    (hl : EnvRep model symbolicLocals locals) :
    output.defined.Holds model ↔ ∃ value, spec.eval params result locals = some value := by
  have h := spec.instantiate_sound hg hp hr hl
  constructor
  · intro hd; obtain ⟨value, hv, _⟩ := h.1 hd; exact ⟨value, hv⟩
  · rintro ⟨value, hv⟩; exact (h.2 value hv).1

theorem Spec.instantiate_value {spec : Spec} {result : Option MValue}
    (hg : spec.instantiate symbolicParams symbolicResult symbolicLocals = some output)
    (hp : EnvRep model symbolicParams params) (hr : ResultRep model symbolicResult result)
    (hl : EnvRep model symbolicLocals locals) :
    spec.eval params result locals = some value ↔ output.Denotes model value := by
  have h := spec.instantiate_sound hg hp hr hl
  constructor
  · exact h.2 value
  · intro hd
    obtain ⟨actual, he, ha⟩ := h.1 hd.1
    have same := ha.eval.symm.trans hd.2.eval
    cases Option.some.inj same
    exact he

end APL.ProductAnnotations
