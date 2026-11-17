import APL.ProductLogicLayout
import APL.FlatProductsFrame

namespace APL.ProductFlow
open ProductLogic
open VCG (MVal Model)

abbrev SymbolsBelow (bound : Nat) (symbols : List SymValue) : Prop :=
  ∀ value ∈ symbols, value.Supported bound

theorem agree_refl : AgreeBelow bound model model := fun _ _ => rfl

theorem agree_trans (ha : AgreeBelow bound a b) (hb : AgreeBelow bound b c) :
    AgreeBelow bound a c := fun i hi => (ha i hi).trans (hb i hi)

theorem agree_restrict (h : AgreeBelow big a b) (hn : small ≤ big) :
    AgreeBelow small a b := fun i hi => h i (Nat.lt_of_lt_of_le hi hn)

theorem value_supported_mono {value : SymValue} (h : value.Supported small) (hn : small ≤ big) :
    value.Supported big := by
  cases value with
  | scalar value => exact value.term.supported_mono h hn
  | tuple fields => intro value hv; exact value.term.supported_mono (h value hv) hn

theorem symbols_supported_mono (h : SymbolsBelow small symbols) (hn : small ≤ big) :
    SymbolsBelow big symbols := fun value hv => value_supported_mono (h value hv) hn

theorem formula_supported_mono {formula : Formula} (h : formula.Supported small) (hn : small ≤ big) :
    formula.Supported big := by
  induction formula with
  | truth => trivial
  | holds term | defined term | boolean term | range term => exact term.supported_mono h hn
  | and a b iha ihb | imp a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | not a ih => exact ih h

def overwrite (model : Model) (index : Nat) (value : MVal) : Model :=
  fun i => if i = index then value else model i

theorem overwrite_agrees : AgreeBelow next model (overwrite model next value) := by
  intro i hi
  simp [overwrite, Nat.ne_of_lt hi]

def scalarDomain (value : SymScalar) : Formula :=
  match value.type with
  | .i64 => .range value.term
  | .bool => .boolean value.term
  | .unit => .defined value.term

def fieldsDomain : List SymScalar → Formula
  | [] => .truth true
  | value :: values => .and (scalarDomain value) (fieldsDomain values)

def valueDomain : SymValue → Formula
  | .scalar value => scalarDomain value
  | .tuple fields => fieldsDomain fields.fields

def envDomain : List SymValue → Formula
  | [] => .truth true
  | value :: values => .and (valueDomain value) (envDomain values)

theorem scalar_domain_sound (h : ScalarDenotes model symbolic (VCG.embed runtime)) :
    (scalarDomain symbolic).Holds model := by
  cases runtime with
  | int n => simp only [VCG.embed] at h; simp only [scalarDomain, h.1]; exact ⟨n.val, h.2, n.property⟩
  | bool b => simp only [VCG.embed] at h; simp only [scalarDomain, h.1]; exact ⟨b, h.2⟩
  | unit => simp only [VCG.embed] at h; simp only [scalarDomain, h.1]; exact ⟨.unit, h.2⟩

theorem fields_domain_sound {values : List APL.Val} (h : FieldsDenote model symbols (values.map VCG.embed)) :
    (fieldsDomain symbols).Holds model := by
  induction values generalizing symbols with
  | nil => cases h; rfl
  | cons value values ih =>
    cases h with
    | cons hv hs => exact ⟨scalar_domain_sound hv, ih hs⟩

theorem value_domain_sound (h : RuntimeDenotes model symbolic runtime) :
    (valueDomain symbolic).Holds model := by
  cases runtime with
  | scalar value => cases h with | scalar h => exact scalar_domain_sound h
  | tuple fields => cases h with | tuple h => exact fields_domain_sound h

theorem env_domain_sound (h : RuntimeEnvRep model symbols values) :
    (envDomain symbols).Holds model := by
  induction values generalizing symbols with
  | nil => cases h; rfl
  | cons value values ih =>
    cases h with
    | cons hv hs => exact ⟨value_domain_sound hv, ih hs⟩

theorem scalar_domain_complete (h : (scalarDomain symbolic).Holds model) :
    ∃ runtime, ScalarDenotes model symbolic (VCG.embed runtime) := by
  cases ht : symbolic.type with
  | i64 =>
    simp only [scalarDomain, ht, Formula.Holds] at h
    obtain ⟨n, hn, hr⟩ := h
    exact ⟨.int ⟨n, hr⟩, ht, hn⟩
  | bool =>
    simp only [scalarDomain, ht, Formula.Holds] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨.bool b, ht, hb⟩
  | unit => exact ⟨.unit, ht, by rw [symbolic.unit_literal ht]; rfl⟩

theorem fields_domain_complete (h : (fieldsDomain symbols).Holds model) :
    ∃ values : List APL.Val, FieldsDenote model symbols (values.map VCG.embed) := by
  induction symbols with
  | nil => exact ⟨[], .nil⟩
  | cons symbol symbols ih =>
    obtain ⟨value, hv⟩ := scalar_domain_complete h.1
    obtain ⟨values, hs⟩ := ih h.2
    exact ⟨value :: values, .cons hv hs⟩

theorem value_domain_complete (h : (valueDomain symbolic).Holds model) :
    ∃ runtime, RuntimeDenotes model symbolic runtime := by
  cases symbolic with
  | scalar symbol =>
    obtain ⟨value, hv⟩ := scalar_domain_complete h
    exact ⟨.scalar value, .scalar hv⟩
  | tuple fields =>
    obtain ⟨values, hv⟩ := fields_domain_complete h
    have hlength : fields.fields.length = values.length := by simpa using hv.length
    let runtime : FlatProducts.Flat APL.Val := ⟨values, by rw [← hlength]; exact fields.nonempty,
      by rw [← hlength]; exact fields.bounded⟩
    exact ⟨.tuple runtime, .tuple hv⟩

theorem env_domain_complete (h : (envDomain symbols).Holds model) :
    ∃ values, RuntimeEnvRep model symbols values := by
  induction symbols with
  | nil => exact ⟨[], .nil⟩
  | cons symbol symbols ih =>
    obtain ⟨value, hv⟩ := value_domain_complete h.1
    obtain ⟨values, hs⟩ := ih h.2
    exact ⟨value :: values, .cons hv hs⟩

def freshScalar (type : APL.Ty) (next : Nat) : SymScalar × Nat :=
  (parameterScalar type next, if type = .unit then next else next + 1)

def freshFields : List APL.Ty → Nat → List SymScalar × Nat
  | [], next => ([], next)
  | type :: types, next =>
      let first := freshScalar type next
      let rest := freshFields types first.2
      (first.1 :: rest.1, rest.2)

theorem fresh_fields_shape : (freshFields types next).1.map SymScalar.type = types := by
  induction types generalizing next with
  | nil => rfl
  | cons type types ih => simp [freshFields, freshScalar, ih]

theorem fresh_fields_length : (freshFields types next).1.length = types.length := by
  have h := congrArg List.length (fresh_fields_shape (types := types) (next := next))
  simpa using h

def freshValue (type : FlatProducts.Ty) (next : Nat) : SymValue × Nat :=
  match type with
  | .scalar type => let first := freshScalar type next; (.scalar first.1, first.2)
  | .tuple shape =>
      let fields := freshFields shape.fields next
      (.tuple ⟨fields.1, by rw [fresh_fields_length]; exact shape.nonempty,
        by rw [fresh_fields_length]; exact shape.bounded⟩, fields.2)

theorem fresh_scalar_bounded : next ≤ (freshScalar type next).2 ∧
    (freshScalar type next).1.Supported (freshScalar type next).2 := by
  cases type <;> simp [freshScalar, parameterScalar, SymScalar.Supported, SymTerm.Supported]

theorem fresh_fields_bounded : next ≤ (freshFields types next).2 ∧
    ∀ field ∈ (freshFields types next).1, field.Supported (freshFields types next).2 := by
  induction types generalizing next with
  | nil => exact ⟨Nat.le_refl _, by simp [freshFields]⟩
  | cons type types ih =>
    have first := fresh_scalar_bounded (type := type) (next := next)
    have rest := ih (next := (freshScalar type next).2)
    refine ⟨Nat.le_trans first.1 rest.1, ?_⟩
    intro field hf
    rcases List.mem_cons.mp hf with rfl | hr
    · exact (freshScalar type next).1.term.supported_mono first.2 rest.1
    · exact rest.2 field hr

theorem fresh_value_shape : (freshValue type next).1.type = type := by
  cases type with
  | scalar type => simp [freshValue, freshScalar, SymValue.type]
  | tuple shape =>
    apply congrArg FlatProducts.Ty.tuple
    apply FlatProducts.Flat.ext
    exact fresh_fields_shape

theorem fresh_value_bounded : next ≤ (freshValue type next).2 ∧
    (freshValue type next).1.Supported (freshValue type next).2 := by
  cases type with
  | scalar type => exact fresh_scalar_bounded
  | tuple shape => exact fresh_fields_bounded

theorem fresh_scalar_covers {value : APL.Val} (ht : value.type = type) (model : Model) :
    ∃ extended, AgreeBelow next model extended ∧
      ScalarDenotes extended (freshScalar type next).1 (VCG.embed value) := by
  cases type with
  | unit =>
    cases value with
    | int n | bool b => cases ht
    | unit => exact ⟨model, agree_refl, rfl, rfl⟩
  | i64 | bool =>
    refine ⟨overwrite model next (VCG.embed value), overwrite_agrees, ?_⟩
    apply parameterScalar_denotes (by simpa using ht)
    intro _
    simp [overwrite]

theorem fresh_fields_covers {values : List APL.Val} (ht : values.map APL.Val.type = types) (model : Model) :
    ∃ extended, AgreeBelow next model extended ∧
      FieldsDenote extended (freshFields types next).1 (values.map VCG.embed) := by
  induction values generalizing types next model with
  | nil => cases ht; exact ⟨model, agree_refl, .nil⟩
  | cons value values ih =>
    cases types with
    | nil => cases ht
    | cons type types =>
      obtain ⟨ht, hts⟩ := List.cons.inj ht
      obtain ⟨middle, hm, hv⟩ := fresh_scalar_covers (next := next) ht model
      obtain ⟨extended, he, hs⟩ := ih (next := (freshScalar type next).2) hts middle
      have hb := fresh_scalar_bounded (type := type) (next := next)
      exact ⟨extended, agree_trans hm (agree_restrict he hb.1),
        .cons (hv.agree hb.2 he) hs⟩

theorem fresh_value_covers {value : FlatProducts.Val} (ht : value.type = type) (model : Model) :
    ∃ extended, AgreeBelow next model extended ∧
      RuntimeDenotes extended (freshValue type next).1 value := by
  cases value with
  | scalar value =>
    cases ht
    obtain ⟨extended, ha, hv⟩ := fresh_scalar_covers (next := next) rfl model
    exact ⟨extended, ha, .scalar hv⟩
  | tuple fields =>
    cases ht
    obtain ⟨extended, ha, hv⟩ := fresh_fields_covers (next := next) (values := fields.fields) rfl model
    exact ⟨extended, ha, .tuple hv⟩

def freshEnv : FlatProducts.Ctx → List SymValue → Nat → Option (List SymValue × Nat)
  | [], [], next => some ([], next)
  | (type, permission) :: context, symbol :: symbols, next => do
      if symbol.type = type then
        let first := if permission then freshValue type next else (symbol, next)
        let rest ← freshEnv context symbols first.2
        return (first.1 :: rest.1, rest.2)
      else none
  | _, _, _ => none

theorem fresh_env_bounded (hgen : freshEnv context symbols start = some (head, finish))
    (hs : SymbolsBelow start symbols) : start ≤ finish ∧ SymbolsBelow finish head := by
  induction context generalizing symbols start head finish with
  | nil =>
    cases symbols with
    | nil => cases hgen; exact ⟨Nat.le_refl _, by intro value hv; cases hv⟩
    | cons => simp [freshEnv] at hgen
  | cons binding context ih =>
    cases symbols with
    | nil => simp [freshEnv] at hgen
    | cons symbol symbols =>
      obtain ⟨type, permission⟩ := binding
      simp only [freshEnv] at hgen
      split at hgen
      next hshape =>
        have first : start ≤ (if permission then freshValue type start else (symbol, start)).2 ∧
            (if permission then freshValue type start else (symbol, start)).1.Supported
              (if permission then freshValue type start else (symbol, start)).2 := by
          cases permission
          · exact ⟨Nat.le_refl _, hs symbol (by simp)⟩
          · exact fresh_value_bounded
        simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
        obtain ⟨⟨tail, last⟩, htail, heq⟩ := hgen
        cases heq
        have hrest : SymbolsBelow start symbols := fun value hv => hs value (by simp [hv])
        obtain ⟨hn, hb⟩ := ih htail (symbols_supported_mono hrest first.1)
        refine ⟨Nat.le_trans first.1 hn, ?_⟩
        intro value hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact value_supported_mono first.2 hn
        · exact hb value hv
      · contradiction

theorem fresh_env_covers (hgen : freshEnv context symbols start = some (head, finish))
    (hs : SymbolsBelow start symbols) (hen : RuntimeEnvRep model symbols entry)
    (hfrozen : FlatProducts.Frozen context entry actual)
    (htyped : FlatProducts.EnvTyped actual context) :
    ∃ extended, AgreeBelow start model extended ∧ RuntimeEnvRep extended head actual := by
  induction hfrozen generalizing symbols start head finish model with
  | nil =>
    cases hen
    cases hgen
    exact ⟨model, agree_refl, .nil⟩
  | @cons permission a b context before after type hsame hfrozen ih =>
    cases hen with
    | @cons symbol _ symbols _ hv henv =>
      have hrest : SymbolsBelow start symbols := fun value hv => hs value (by simp [hv])
      simp only [freshEnv] at hgen
      split at hgen
      next hshape =>
        cases permission with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
          obtain ⟨⟨tail, last⟩, htail, heq⟩ := hgen
          cases heq
          obtain ⟨extended, ha, he⟩ := ih htail hrest henv (FlatProducts.env_tail htyped)
          have same := hsame rfl
          subst b
          exact ⟨extended, ha, .cons (hv.agree (hs symbol (by simp)) ha) he⟩
        | true =>
          simp only [↓reduceIte, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
          obtain ⟨⟨tail, last⟩, htail, heq⟩ := hgen
          cases heq
          have ht : b.type = type := (List.cons.inj htyped).1
          have hb := fresh_value_bounded (type := type) (next := start)
          obtain ⟨middle, hm, hv⟩ := fresh_value_covers (next := start) ht model
          obtain ⟨extended, ha, he⟩ := ih htail (symbols_supported_mono hrest hb.1)
            (henv.agree hrest hm) (FlatProducts.env_tail htyped)
          exact ⟨extended, agree_trans hm (agree_restrict ha hb.1), .cons (hv.agree hb.2 ha) he⟩
      · contradiction

structure Head where
  symbols : List SymValue
  domain : Formula
  next : Nat

def freshHead (context : FlatProducts.Ctx) (symbols : List SymValue) (start : Nat) : Option Head := do
  let (values, finish) ← freshEnv context symbols start
  return ⟨values, envDomain values, finish⟩

theorem fresh_head_coverage (hgen : freshHead context symbols start = some head)
    (hs : SymbolsBelow start symbols) (hen : RuntimeEnvRep model symbols entry)
    (hfrozen : FlatProducts.Frozen context entry actual)
    (htyped : FlatProducts.EnvTyped actual context) :
    start ≤ head.next ∧ SymbolsBelow head.next head.symbols ∧
      ∃ extended, AgreeBelow start model extended ∧
        RuntimeEnvRep extended head.symbols actual ∧ head.domain.Holds extended := by
  simp only [freshHead, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨symbols, finish⟩, hfresh, heq⟩ := hgen
  cases heq
  obtain ⟨hn, hb⟩ := fresh_env_bounded hfresh hs
  obtain ⟨extended, ha, he⟩ := fresh_env_covers hfresh hs hen hfrozen htyped
  exact ⟨hn, hb, extended, ha, he, env_domain_sound he⟩

def scalarFreshCount : APL.Ty → Nat
  | .unit => 0
  | _ => 1

def fieldsFreshCount : List APL.Ty → Nat
  | [] => 0
  | type :: types => scalarFreshCount type + fieldsFreshCount types

def valueFreshCount : FlatProducts.Ty → Nat
  | .scalar type => scalarFreshCount type
  | .tuple shape => fieldsFreshCount shape.fields

def scalarHeadIds (value : SymScalar) : List Nat :=
  match value.type, value.term with
  | .unit, _ => []
  | _, .var index => [index]
  | _, _ => []

def valueHeadIds : SymValue → List Nat
  | .scalar value => scalarHeadIds value
  | .tuple fields => fields.fields.flatMap scalarHeadIds

theorem fresh_scalar_identities :
    (freshScalar type start).2 = start + scalarFreshCount type ∧
    scalarHeadIds (freshScalar type start).1 = List.range' start (scalarFreshCount type) := by
  cases type <;> simp [freshScalar, scalarFreshCount, scalarHeadIds, parameterScalar, List.range'_succ]

theorem fresh_fields_identities :
    (freshFields types start).2 = start + fieldsFreshCount types ∧
    (freshFields types start).1.flatMap scalarHeadIds = List.range' start (fieldsFreshCount types) := by
  induction types generalizing start with
  | nil => simp [freshFields, fieldsFreshCount]
  | cons type types ih =>
    have hfirst := fresh_scalar_identities (type := type) (start := start)
    have hrest := ih (start := (freshScalar type start).2)
    constructor
    · change (freshFields types (freshScalar type start).2).2 = _
      rw [hrest.1, hfirst.1]
      simp [fieldsFreshCount, Nat.add_assoc]
    · change scalarHeadIds (freshScalar type start).1 ++
        (freshFields types (freshScalar type start).2).1.flatMap scalarHeadIds = _
      rw [hfirst.2, hrest.2, hfirst.1]
      simp [fieldsFreshCount]

theorem fresh_value_identities :
    (freshValue type start).2 = start + valueFreshCount type ∧
    valueHeadIds (freshValue type start).1 = List.range' start (valueFreshCount type) := by
  cases type with
  | scalar type => exact fresh_scalar_identities
  | tuple shape => exact fresh_fields_identities

def freshCount : FlatProducts.Ctx → Nat
  | [] => 0
  | (type, permission) :: context => (if permission then valueFreshCount type else 0) + freshCount context

def headIds : FlatProducts.Ctx → List SymValue → Option (List Nat)
  | [], [] => some []
  | (_, permission) :: context, symbol :: symbols => do
      let rest ← headIds context symbols
      return (if permission then valueHeadIds symbol else []) ++ rest
  | _, _ => none

theorem fresh_env_identities (hgen : freshEnv context symbols start = some (head, finish)) :
    finish = start + freshCount context ∧
    headIds context head = some (List.range' start (freshCount context)) := by
  induction context generalizing symbols start head finish with
  | nil =>
    cases symbols with
    | nil => cases hgen; simp [freshCount, headIds]
    | cons => simp [freshEnv] at hgen
  | cons binding context ih =>
    cases symbols with
    | nil => simp [freshEnv] at hgen
    | cons symbol symbols =>
      obtain ⟨type, permission⟩ := binding
      simp only [freshEnv] at hgen
      split at hgen
      next hshape =>
        simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
        obtain ⟨⟨tail, last⟩, htail, heq⟩ := hgen
        cases heq
        obtain ⟨hn, hi⟩ := ih htail
        cases permission with
        | false => simp [freshCount, headIds, hn, hi]
        | true =>
          have hfirst := fresh_value_identities (type := type) (start := start)
          constructor
          · simpa [freshCount, hfirst.1, Nat.add_assoc] using hn
          · simp only [headIds, hi, bind, Option.bind_some, ↓reduceIte, Option.pure_def, hfirst.2, hfirst.1, freshCount]
            congr 1
            simp
      · contradiction

theorem fresh_env_distinct (hgen : freshEnv context symbols start = some (head, finish)) :
    ∃ ids, headIds context head = some ids ∧ ids.Nodup ∧
      ∀ index ∈ ids, start ≤ index ∧ index < finish := by
  obtain ⟨hn, hi⟩ := fresh_env_identities hgen
  refine ⟨List.range' start (freshCount context), hi, List.nodup_range', ?_⟩
  intro index member
  rw [List.mem_range'_1] at member
  exact ⟨member.1, hn ▸ member.2⟩

theorem fresh_env_disjoint
    (ha : freshEnv a symbolsA start = some (headA, middle))
    (hb : freshEnv b symbolsB middle = some (headB, finish))
    (hia : headIds a headA = some idsA) (hib : headIds b headB = some idsB) :
    ∀ index ∈ idsA, index ∉ idsB := by
  obtain ⟨_, haids, _, hab⟩ := fresh_env_distinct ha
  obtain ⟨_, hbids, _, hbb⟩ := fresh_env_distinct hb
  rw [hia] at haids
  rw [hib] at hbids
  cases haids
  cases hbids
  intro index hai hbi
  have a := hab index hai
  have b := hbb index hbi
  omega

end APL.ProductFlow
