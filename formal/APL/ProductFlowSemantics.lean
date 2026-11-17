import APL.ProductFlowBounds
import APL.FlatProductsContinuation

namespace APL.ProductFlow
open ProductLogic
open VCG (Model)
open FlatProducts.LoopVerification

theorem valid_member (h : ValidFrom bound model checks) (member : check ∈ checks)
    (ha : AgreeBelow bound model extended) (hg : check.guard.Holds extended) :
    check.required.Holds extended := group_exact.mp (h extended ha) check member hg

theorem valid_subset (h : ValidFrom bound model checks)
    (hs : ∀ check ∈ subset, check ∈ checks) : ValidFrom bound model subset := by
  intro extended ha
  apply group_exact.mpr
  intro check member hg
  exact valid_member h (hs check member) ha hg

theorem valid_extend (h : ValidFrom bound model checks)
    (ha : AgreeBelow bound model nextModel) (hn : bound ≤ nextBound) :
    ValidFrom nextBound nextModel checks := by
  intro extended hnext
  exact h extended (agree_trans ha (agree_restrict hnext hn))

theorem covered_extend (h : Covered nextBound nextModel analysis value env)
    (ha : AgreeBelow bound model nextModel) (hn : bound ≤ nextBound) :
    Covered bound model analysis value env := by
  obtain ⟨extended, he, hp, hv, henv⟩ := h
  exact ⟨extended, agree_trans ha (agree_restrict he hn), hp, hv, henv⟩

theorem runtime_denotes_type (h : RuntimeDenotes model symbol value) : symbol.type = value.type := by
  simpa using h.shape

theorem runtime_env_types (h : RuntimeEnvRep model symbols values) :
    symbols.map SymValue.type = values.map FlatProducts.Val.type := by
  simpa [List.map_map, Function.comp_def] using h.shape

theorem merge_fields_shape (hg : mergeFields condition left right = some fields) :
    left.map SymScalar.type = right.map SymScalar.type := by
  induction left generalizing right fields with
  | nil => cases right with
    | nil => rfl
    | cons => simp [mergeFields] at hg
  | cons a left ih =>
    cases right with
    | nil => simp [mergeFields] at hg
    | cons b right =>
      simp only [mergeFields, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨value, hv, fields, hf, heq⟩ := hg
      simp [mergeScalar_shape hv, ih hf]

theorem merge_inputs_shape (hg : merge condition left right = some value) : left.type = right.type := by
  cases left with
  | scalar left =>
    cases right with
    | scalar right =>
      simp only [merge, Option.map_eq_some_iff] at hg
      obtain ⟨value, hv, _⟩ := hg
      exact congrArg FlatProducts.Ty.scalar (mergeScalar_shape hv).2
    | tuple right => simp [merge] at hg
  | tuple left =>
    cases right with
    | scalar right => simp [merge] at hg
    | tuple right =>
      simp only [merge, bind, Option.bind_eq_some_iff] at hg
      obtain ⟨fields, hf, _⟩ := hg
      exact congrArg FlatProducts.Ty.tuple (FlatProducts.Flat.ext (merge_fields_shape hf))

theorem merge_env_inputs_shape (hg : mergeEnv condition left right = some env) :
    left.map SymValue.type = right.map SymValue.type := by
  induction left generalizing right env with
  | nil => cases right with
    | nil => rfl
    | cons => simp [mergeEnv] at hg
  | cons a left ih =>
    cases right with
    | nil => simp [mergeEnv] at hg
    | cons b right =>
      simp only [mergeEnv, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨value, hv, env, he, _⟩ := hg
      simp [merge_inputs_shape hv, ih he]

theorem merge_flow_covered (hg : mergeFlow condition yes no = some output)
    (hc : condition.eval model = some (.bool selected)) (hb : condition.Supported bound)
    (hv : Covered bound model (if selected then yes else no) value env) :
    Covered bound model output value env := by
  simp only [mergeFlow, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨symbol, hs, symbols, he, heq⟩ := hg
  cases heq
  obtain ⟨extended, ha, hp, hv, henv⟩ := hv
  have hc' : condition.eval extended = some (.bool selected) := (condition.eval_agree hb ha).symm.trans hc
  have hv' : ProductDenotes extended (if selected then yes.value else no.value) (embedValue value) := by
    cases selected <;> exact hv
  have henv' : EnvRep extended (if selected then yes.env else no.env) (env.map embedValue) := by
    cases selected <;> exact henv
  obtain ⟨result, hr, hrep⟩ := merge_selected hv' (merge_inputs_shape hs) hc'
  obtain ⟨values, hvs, hreps⟩ := mergeEnv_selected henv' (merge_env_inputs_shape he) hc'
  rw [hs] at hr
  rw [he] at hvs
  cases hr
  cases hvs
  refine ⟨extended, ha, ?_, hrep, hreps⟩
  intro hnot
  cases selected with
  | false => exact hnot.2 hp
  | true => exact hnot.1 hp

theorem update_runtime (hg : updateSymbols symbols index symbol = some finalSymbols)
    (he : RuntimeEnvRep model symbols env) (hv : RuntimeDenotes model symbol value) :
    ∃ final, FlatProducts.update env index value = some final ∧ RuntimeEnvRep model finalSymbols final := by
  induction env generalizing symbols index finalSymbols with
  | nil => cases he; simp [updateSymbols] at hg
  | cons old env ih =>
    cases he with
    | cons ho he =>
      cases index with
      | zero => cases hg; exact ⟨value :: env, rfl, .cons hv he⟩
      | succ index =>
        simp only [updateSymbols, Option.map_eq_some_iff] at hg
        obtain ⟨rest, hr, rfl⟩ := hg
        obtain ⟨final, hu, hf⟩ := ih hr he
        exact ⟨old :: final, by simp [FlatProducts.update, hu], .cons ho hf⟩

theorem as_boolean_sound (hg : asBoolean symbol = some term) (hv : RuntimeDenotes model symbol value) :
    ∃ test, value = .scalar (.bool test) ∧ term.eval model = some (.bool test) := by
  cases symbol with
  | tuple fields => simp [asBoolean] at hg
  | scalar symbol =>
    simp only [asBoolean] at hg
    split at hg
    next ht =>
      cases hg
      cases value with
      | tuple fields => cases hv
      | scalar value =>
        cases hv with
        | scalar hv =>
          have ht' : value.type = .bool := by simpa using hv.1.symm.trans ht
          cases value with
          | int n | unit => cases ht'
          | bool test => exact ⟨test, rfl, hv.2⟩
    · contradiction

theorem as_scalars_denote {values : List APL.Val} (hg : symbols.mapM asScalar = some fields)
    (hr : RuntimeEnvRep model symbols (values.map FlatProducts.Val.scalar)) :
    FieldsDenote model fields (values.map VCG.embed) := by
  induction values generalizing symbols fields with
  | nil => cases hr; cases hg; exact .nil
  | cons value values ih =>
    cases hr with
    | cons hv hr =>
      cases hv with
      | scalar hv =>
        simp only [List.mapM_cons, asScalar, bind, Option.bind_some, Option.bind_eq_some_iff, Option.pure_def] at hg
        obtain ⟨rest, hg, heq⟩ := hg
        cases heq
        exact .cons hv (ih hg hr)

theorem runtime_tuple_value {values : List APL.Val} (hg : tupleSymbol symbols = some symbol)
    (hr : RuntimeEnvRep model symbols (values.map FlatProducts.Val.scalar)) :
    ∃ actual, FlatProducts.construct values = .value actual ∧ RuntimeDenotes model symbol actual := by
  simp only [tupleSymbol, bind, Option.bind_eq_some_iff, construct, Option.map_eq_some_iff] at hg
  obtain ⟨fields, hf, product, hp, rfl⟩ := hg
  have hd := as_scalars_denote hf hr
  have hfields := FlatProducts.make_fields hp
  have hlength : fields.length = values.length := by simpa using hd.length
  let actual : FlatProducts.Flat APL.Val := ⟨values,
    by rw [← hlength, ← hfields]; exact product.nonempty,
    by rw [← hlength, ← hfields]; exact product.bounded⟩
  refine ⟨.tuple actual, ?_, .tuple (hfields ▸ hd)⟩
  change (match FlatProducts.Flat.make actual.fields with
    | some fields => FlatProducts.Result.value (.tuple fields)
    | none => .invalid) = _
  simp

theorem runtime_project_value (hg : project symbol index = some field)
    (hr : RuntimeDenotes model symbol value) :
    ∃ actual, FlatProducts.project value index = .value actual ∧
      RuntimeDenotes model (.scalar field) actual := by
  cases value with
  | scalar value => cases hr with | scalar hr => simp [project] at hg
  | tuple fields =>
    cases hr with
    | tuple hr =>
      obtain ⟨actual, ha, hrep⟩ := ProductAnnotations.fields_lookup_symbol hr hg
      simp only [FlatProducts.Flat.map, List.getElem?_map] at ha
      cases hvalue : fields.fields[index]? with
      | none => simp [hvalue] at ha
      | some value =>
        simp only [hvalue, Option.map_some, Option.some.injEq] at ha
        subst actual
        exact ⟨.scalar value, by simp [FlatProducts.project, hvalue], .scalar hrep⟩

theorem args_fields_spec {types : List APL.Ty} (wf : FlatProducts.WellTyped fs)
    (ht : FlatProducts.ArgsTyped (FlatProducts.signatures fs) context terms (types.map FlatProducts.Ty.scalar))
    (he : FlatProducts.EnvTyped env context) (hs : ArgsSpec fs terms env result) :
    FieldsSpec fs terms env (fun values final => result (values.map FlatProducts.Val.scalar) final) := by
  induction terms generalizing types env result with
  | nil => exact hs
  | cons term terms ih =>
    obtain ⟨type, rest, rfl, ht, hts⟩ := FlatProducts.args_scalar_cons ht
    apply spec_mono (spec_frame hs wf ht he)
    intro value final hout
    obtain ⟨scalar, rfl, _⟩ := FlatProducts.scalar_canonical hout.2.2.2
    exact ⟨scalar, rfl, ih hts hout.2.2.1 hout.1⟩

def SoundAt (fs : FlatProducts.Functions) (term : FlatProducts.Term) (context : FlatProducts.Ctx)
    (symbols : List SymValue) (path : Formula) (start : Nat) (flow : Analysis SymValue) : Prop :=
  ∀ model env, RuntimeEnvRep model symbols env → FlatProducts.EnvTyped env context → path.Holds model →
    ValidFrom start model flow.checks → EvalSpec fs term env (Covered start model flow)

theorem arguments_sound {types : List FlatProducts.Ty}
    (wf : FlatProducts.WellTyped fs)
    (bounded : ∀ term symbols path start site output, generate term symbols path start site = some output →
      SymbolsBelow start symbols → path.Supported start → start ≤ output.next ∧ output.Bounded)
    (sound : ∀ term symbols path start site output, generate term symbols path start site = some output →
      SymbolsBelow start symbols → path.Supported start →
      SoundAt fs term.erase context symbols path start output)
    (hg : arguments generate terms symbols path start site index = some output)
    (ht : FlatProducts.ArgsTyped (FlatProducts.signatures fs) context
      (terms.map ProductAnnotations.Term.erase) types)
    (hs : SymbolsBelow start symbols) (hpath : path.Supported start)
    (he : RuntimeEnvRep model symbols env) (hen : FlatProducts.EnvTyped env context)
    (hp : path.Holds model) (valid : ValidFrom start model output.checks) :
    ArgsSpec fs (terms.map ProductAnnotations.Term.erase) env (ArgsCovered start model output) := by
  induction terms generalizing types symbols path start index output model env with
  | nil =>
    cases hg
    exact ⟨model, agree_refl, hp, .nil, he⟩
  | cons term terms ih =>
    simp only [arguments, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, hf, rest, hr, heq⟩ := hg
    cases heq
    cases ht with
    | cons ht hts =>
      obtain ⟨hn, hb⟩ := bounded term symbols path start _ first hf hs hpath
      have firstValid : ValidFrom start model first.checks :=
        valid_subset valid (fun check hc => List.mem_append_left _ hc)
      have firstSpec := sound term symbols path start _ first hf hs hpath model env he hen hp firstValid
      apply spec_mono (spec_frame firstSpec wf ht hen)
      intro value current hout
      obtain ⟨middle, hm, hp, hv, hcurrent⟩ := hout.1
      have restValid : ValidFrom first.next middle rest.checks :=
        valid_extend (valid_subset valid (fun check hc => List.mem_append_right _ hc)) hm hn
      have tail := ih hr hts hb.2.1 hb.2.2 hcurrent hout.2.2.1 hp restValid
      apply args_spec_mono tail
      intro values final hfinal
      obtain ⟨extended, ha, hnormal, hvalues, henv⟩ := hfinal
      exact ⟨extended, agree_trans hm (agree_restrict ha hn), hnormal,
        .cons (hv.agree hb.1 ha) hvalues, henv⟩

end APL.ProductFlow
