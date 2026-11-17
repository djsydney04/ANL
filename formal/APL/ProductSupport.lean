import APL.ProductClauses

namespace APL.ProductFlow
open ProductLogic
open ProductAnnotations

abbrev FieldsBelow (bound : Nat) (fields : List SymScalar) : Prop :=
  ∀ field ∈ fields, field.Supported bound

theorem supported_lookup (hs : SymbolsBelow bound symbols)
    (hg : symbols[(index : Nat)]? = some symbol) : symbol.Supported bound :=
  hs symbol (List.mem_of_getElem? hg)

theorem construct_supported (hg : construct fields = some value) (hs : FieldsBelow bound fields) :
    value.Supported bound := by
  simp only [construct, Option.map_eq_some_iff] at hg
  obtain ⟨product, hp, rfl⟩ := hg
  have hf := FlatProducts.make_fields hp
  intro field member
  rw [hf] at member
  exact hs field member

theorem project_supported (hg : project value index = some field) (hs : value.Supported bound) :
    field.Supported bound := by
  cases value with
  | scalar => simp [project] at hg
  | tuple fields => exact hs field (List.mem_of_getElem? hg)

theorem equality_fields_supported (hg : equalityFields left right = some term)
    (hl : FieldsBelow bound left) (hr : FieldsBelow bound right) : term.Supported bound := by
  induction left generalizing right term with
  | nil => cases right with
    | nil => cases hg; trivial
    | cons => simp [equalityFields] at hg
  | cons a left ih =>
    cases right with
    | nil => simp [equalityFields] at hg
    | cons b right =>
      simp only [equalityFields, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨rest, hg, heq⟩ := hg
      cases heq
      exact ⟨⟨hl a (by simp), hr b (by simp)⟩,
        ih hg (fun value hv => hl value (by simp [hv])) (fun value hv => hr value (by simp [hv]))⟩

theorem equality_supported (hg : equality left right = some term)
    (hl : left.Supported bound) (hr : right.Supported bound) : term.Supported bound := by
  simp only [equality] at hg
  split at hg
  · cases left <;> cases right
    · cases hg; exact ⟨hl, hr⟩
    · contradiction
    · contradiction
    · exact equality_fields_supported hg hl hr
  · contradiction

theorem inequality_supported (hg : inequality left right = some term)
    (hl : left.Supported bound) (hr : right.Supported bound) : term.Supported bound := by
  simp only [inequality, Option.map_eq_some_iff] at hg
  obtain ⟨term, ht, rfl⟩ := hg
  change term.Supported bound
  exact equality_supported ht hl hr

theorem scalar_domain_supported (h : symbol.Supported bound) : (scalarDomain symbol).Supported bound := by
  cases ht : symbol.type <;> simpa only [scalarDomain, ht, Formula.Supported, SymScalar.Supported] using h

theorem fields_domain_supported (h : FieldsBelow bound fields) : (fieldsDomain fields).Supported bound := by
  induction fields with
  | nil => trivial
  | cons field fields ih => exact ⟨scalar_domain_supported (h field (by simp)),
      ih (fun value hv => h value (by simp [hv]))⟩

theorem value_domain_supported (h : value.Supported bound) : (valueDomain value).Supported bound := by
  cases value with
  | scalar value => exact scalar_domain_supported h
  | tuple fields => exact fields_domain_supported h

theorem env_domain_supported (h : SymbolsBelow bound symbols) : (envDomain symbols).Supported bound := by
  induction symbols with
  | nil => trivial
  | cons value symbols ih => exact ⟨value_domain_supported (h value (by simp)),
      ih (fun value hv => h value (by simp [hv]))⟩

theorem merge_scalar_supported (hg : mergeScalar condition left right = some value)
    (hc : condition.Supported bound) (hl : left.Supported bound) (hr : right.Supported bound) :
    value.Supported bound := by
  simp only [mergeScalar] at hg
  split at hg
  · cases hg
    simp only [SymScalar.Supported]
    split
    · trivial
    · exact ⟨hc, hl, hr⟩
  · contradiction

theorem merge_fields_supported (hg : mergeFields condition left right = some fields)
    (hc : condition.Supported bound) (hl : FieldsBelow bound left) (hr : FieldsBelow bound right) :
    FieldsBelow bound fields := by
  induction left generalizing right fields with
  | nil => cases right with
    | nil => cases hg; intro value hv; cases hv
    | cons => simp [mergeFields] at hg
  | cons a left ih =>
    cases right with
    | nil => simp [mergeFields] at hg
    | cons b right =>
      simp only [mergeFields, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨value, hv, fields, hf, heq⟩ := hg
      cases heq
      intro field member
      rcases List.mem_cons.mp member with rfl | member
      · exact merge_scalar_supported hv hc (hl a (by simp)) (hr b (by simp))
      · exact ih hf (fun value hv => hl value (by simp [hv]))
          (fun value hv => hr value (by simp [hv])) field member

theorem merge_supported (hg : merge condition left right = some value)
    (hc : condition.Supported bound) (hl : left.Supported bound) (hr : right.Supported bound) :
    value.Supported bound := by
  cases left with
  | scalar left =>
    cases right with
    | scalar right =>
      simp only [merge, Option.map_eq_some_iff] at hg
      obtain ⟨value, hv, rfl⟩ := hg
      exact merge_scalar_supported hv hc hl hr
    | tuple right => simp [merge] at hg
  | tuple left =>
    cases right with
    | scalar right => simp [merge] at hg
    | tuple right =>
      simp only [merge, bind, Option.bind_eq_some_iff] at hg
      obtain ⟨fields, hf, hp⟩ := hg
      exact construct_supported hp (merge_fields_supported hf hc hl hr)

theorem merge_env_supported (hg : mergeEnv condition left right = some values)
    (hc : condition.Supported bound) (hl : SymbolsBelow bound left) (hr : SymbolsBelow bound right) :
    SymbolsBelow bound values := by
  induction left generalizing right values with
  | nil => cases right with
    | nil => cases hg; intro value hv; cases hv
    | cons => simp [mergeEnv] at hg
  | cons a left ih =>
    cases right with
    | nil => simp [mergeEnv] at hg
    | cons b right =>
      simp only [mergeEnv, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨value, hv, values, hvs, heq⟩ := hg
      cases heq
      intro value' member
      rcases List.mem_cons.mp member with rfl | member
      · exact merge_supported hv hc (hl a (by simp)) (hr b (by simp))
      · exact ih hvs (fun value hv => hl value (by simp [hv]))
          (fun value hv => hr value (by simp [hv])) value' member

end APL.ProductFlow

namespace APL.ProductAnnotations
open ProductLogic ProductFlow

def Instantiated.Supported (bound : Nat) (value : Instantiated) : Prop :=
  value.value.Supported bound ∧ value.defined.Supported bound

def Clause.Supported (bound : Nat) (value : Clause) : Prop :=
  value.defined.Supported bound ∧ value.truth.Supported bound

theorem short_guard_supported (h : term.Supported bound) :
    (shortGuard op term).Supported bound := by
  cases op <;> first | exact h | trivial

theorem instantiate_unary_supported (hg : instantiateUnary op input = some output)
    (h : input.Supported bound) : output.Supported bound := by
  cases input with
  | mk value defined =>
    cases value with
    | tuple fields => simp [instantiateUnary] at hg
    | scalar value =>
      simp only [instantiateUnary] at hg
      split at hg
      · cases hg; exact ⟨h.1, h.2, h.1⟩
      · contradiction

theorem instantiate_binary_supported (hg : instantiateBinary op left right = some output)
    (hl : left.Supported bound) (hr : right.Supported bound) : output.Supported bound := by
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
          exact ⟨⟨hl.1, hr.1⟩, hl.2, ⟨short_guard_supported hl.1, hr.2⟩, hl.1, hr.1⟩
        | tuple right => simp [instantiateBinary, SymValue.type, FlatProducts.binaryType] at hg
      | tuple left =>
        cases right with
        | scalar right => simp [instantiateBinary, SymValue.type, FlatProducts.binaryType] at hg
        | tuple right =>
          simp only [instantiateBinary, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
          obtain ⟨type, _, term, ht, heq⟩ := hg
          cases heq
          have hs : term.Supported bound := by
            split at ht
            · exact inequality_supported ht hl.1 hr.1
            · exact equality_supported ht hl.1 hr.1
          exact ⟨hs, hl.2, hr.2⟩

theorem mapM_property {inputs : List α} {outputs : List β} {f : α → Option β} {predicate : β → Prop} (hg : inputs.mapM f = some outputs)
    (h : ∀ input ∈ inputs, ∀ output, f input = some output → predicate output) :
    ∀ output ∈ outputs, predicate output := by
  induction inputs generalizing outputs with
  | nil => cases hg; intro output ho; cases ho
  | cons input inputs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨output, ho, rest, hr, heq⟩ := hg
    cases heq
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact h input (by simp) _ ho
    · exact ih hr (fun input hi => h input (by simp [hi])) value member

theorem all_defined_supported (h : ∀ value ∈ values, value.Supported bound) :
    (allDefined values).Supported bound := by
  induction values with
  | nil => trivial
  | cons value values ih => exact ⟨(h value (by simp)).2,
      ih (fun value hv => h value (by simp [hv]))⟩

theorem instantiated_scalar_supported (hg : instantiatedScalar value = some scalar)
    (h : value.Supported bound) : scalar.Supported bound := by
  cases value with
  | mk value defined =>
    cases value with
    | scalar symbol => cases hg; exact h.1
    | tuple fields => simp [instantiatedScalar] at hg

theorem instantiate_tuple_supported (hg : instantiateTuple values = some output)
    (h : ∀ value ∈ values, value.Supported bound) : output.Supported bound := by
  simp only [instantiateTuple, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨fields, hf, product, hp, heq⟩ := hg
  cases heq
  exact ⟨construct_supported hp (mapM_property hf (fun value hv field hg =>
    instantiated_scalar_supported hg (h value hv))), all_defined_supported h⟩

theorem instantiate_project_supported (hg : instantiateProject input index = some output)
    (h : input.Supported bound) : output.Supported bound := by
  simp only [instantiateProject, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨field, hf, heq⟩ := hg
  cases heq
  exact ⟨project_supported hf h.1, h.2⟩

theorem Spec.instantiate_supported {spec : Spec} {result : Option SymValue}
    (hg : spec.instantiate params result locals = some output)
    (hp : SymbolsBelow bound params) (hr : ∀ value, result = some value → value.Supported bound)
    (hl : SymbolsBelow bound locals) : output.Supported bound := by
  induction spec using Spec.rec
    (motive_2 := fun specs => ∀ outputs,
      specs.mapM (Spec.instantiate params result locals) = some outputs →
      ∀ value ∈ outputs, value.Supported bound) generalizing output with
  | lit value =>
    simp only [Spec.instantiate, Option.some.injEq] at hg
    subst output
    exact ⟨trivial, trivial⟩
  | param index =>
    simp only [Spec.instantiate, Option.map_eq_some_iff] at hg
    obtain ⟨symbol, hs, rfl⟩ := hg
    exact ⟨supported_lookup hp hs, trivial⟩
  | result =>
    simp only [Spec.instantiate, Option.map_eq_some_iff] at hg
    obtain ⟨symbol, hs, rfl⟩ := hg
    exact ⟨hr symbol hs, trivial⟩
  | «local» index =>
    simp only [Spec.instantiate, Option.map_eq_some_iff] at hg
    obtain ⟨symbol, hs, rfl⟩ := hg
    exact ⟨supported_lookup hl hs, trivial⟩
  | unary op operand ih =>
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨input, hi, hg⟩ := hg
    exact instantiate_unary_supported hg (ih hi)
  | binary op left right iha ihb =>
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨left, ha, right, hb, hg⟩ := hg
    exact instantiate_binary_supported hg (iha ha) (ihb hb)
  | tuple fields ih =>
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨fields, hf, hg⟩ := hg
    exact instantiate_tuple_supported hg (ih fields hf)
  | project base index ih =>
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨base, hb, hg⟩ := hg
    exact instantiate_project_supported hg (ih hb)
  | nil outputs hg value hv => cases hg; cases hv
  | cons spec specs ih ihs outputs hg value hv =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨output, ho, outputs, hos, heq⟩ := hg
    cases heq
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ih ho
    · exact ihs outputs hos value hv

theorem boolean_clause_supported (hg : booleanClause input = some clause)
    (h : input.Supported bound) : clause.Supported bound := by
  cases input with
  | mk value defined =>
    cases value with
    | tuple fields => simp [booleanClause] at hg
    | scalar value =>
      simp only [booleanClause] at hg
      split at hg
      · cases hg; exact ⟨⟨h.2, h.1⟩, h.2, h.1⟩
      · contradiction

theorem Spec.clause_supported {spec : Spec} {clause : Clause} {result : Option SymValue}
    (hg : spec.clause params result locals = some clause)
    (hp : SymbolsBelow bound params) (hr : ∀ value, result = some value → value.Supported bound)
    (hl : SymbolsBelow bound locals) : clause.Supported bound := by
  simp only [Spec.clause, bind, Option.bind_eq_some_iff] at hg
  obtain ⟨input, hi, hg⟩ := hg
  exact boolean_clause_supported hg (spec.instantiate_supported hi hp hr hl)

theorem requires_supported (hg : requiresVC symbols clauses = some output)
    (h : SymbolsBelow bound symbols) : output.Supported bound := by
  induction clauses generalizing output with
  | nil => cases hg; exact ⟨trivial, trivial⟩
  | cons clause clauses ih =>
    simp only [requiresVC, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, hf, rest, hr, heq⟩ := hg
    cases heq
    have first := clause.clause_supported hf h (by intro value hv; cases hv) (by intro value hv; cases hv)
    have rest := ih hr
    exact ⟨⟨first.1, first.2, rest.1⟩, first.2, rest.2⟩

theorem assertions_supported (hg : assertionsVC params result locals clauses = some outputs)
    (hp : SymbolsBelow bound params) (hr : ∀ value, result = some value → value.Supported bound)
    (hl : SymbolsBelow bound locals) : ∀ clause ∈ outputs, clause.Supported bound := by
  induction clauses generalizing outputs with
  | nil => cases hg; intro value hv; cases hv
  | cons clause clauses ih =>
    simp only [assertionsVC, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, hf, rest, hrest, heq⟩ := hg
    cases heq
    intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact clause.clause_supported hf hp hr hl
    · exact ih hrest value hv

theorem clause_conjunction_supported (h : ∀ clause ∈ clauses, clause.Supported bound) :
    (clauseConjunction clauses).Supported bound := by
  induction clauses with
  | nil => trivial
  | cons clause clauses ih => exact ⟨(h clause (by simp)).2,
      ih (fun value hv => h value (by simp [hv]))⟩

end APL.ProductAnnotations
