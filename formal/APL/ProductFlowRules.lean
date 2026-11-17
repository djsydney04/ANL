import APL.ProductFlowLoops

namespace APL.ProductFlow
open ProductLogic
open VCG (Model)
open FlatProducts.LoopVerification

theorem literal_sound : SoundAt fs (.lit value) context symbols path start
    (single (runtimeLiteral value) symbols path start) := by
  intro model env he _ hp _
  apply spec_mono literal_rule
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨model, agree_refl, hp, runtime_literal_denotes, he⟩

theorem local_sound (hg : symbols[index]? = some symbol) :
    SoundAt fs (.local index) context symbols path start (single symbol symbols path start) := by
  intro model env he _ hp _
  obtain ⟨value, hv, hrep⟩ := ProductAnnotations.env_lookup_symbol he hg
  simp only [List.getElem?_map] at hv
  cases hget : env[index]? with
  | none => simp [hget] at hv
  | some actual =>
    simp only [hget, Option.map_some, Option.some.injEq] at hv
    subst value
    apply spec_mono (local_rule hget)
    rintro _ _ ⟨rfl, rfl⟩
    exact ⟨model, agree_refl, hp, hrep, he⟩

theorem assignment_analysis_sound
    (hc : SoundAt fs rhs context symbols path start first)
    (hg : updateSymbols first.env index first.value = some finalSymbols) :
    SoundAt fs (.assign index rhs) context symbols path start
      { first with value := runtimeLiteral (.scalar .unit), env := finalSymbols } := by
  intro model env he ht hp valid
  apply assignment_rule
  apply spec_mono (hc model env he ht hp valid)
  intro value current hout
  obtain ⟨extended, ha, hp, hv, he⟩ := hout
  obtain ⟨final, hu, he⟩ := update_runtime hg he hv
  exact ⟨final, hu, extended, ha, hp, runtime_literal_denotes (value := .scalar .unit), he⟩

theorem unary_analysis_sound
    (hc : SoundAt fs arg context symbols path start first)
    (hg : runtimeUnary op first.value = some result) :
    SoundAt fs (.unary op arg) context symbols path start
      (addCheck .body first.normal result.defined { first with value := result.value }) := by
  intro model env he ht hp valid
  have childValid : ValidFrom start model first.checks :=
    valid_subset valid (fun _ hc => List.mem_append_left _ hc)
  apply unary_rule
  apply spec_mono (hc model env he ht hp childValid)
  intro value current hout
  obtain ⟨extended, ha, hp, hv, he⟩ := hout
  have guard := valid_member valid (check := ⟨.body, first.normal, result.defined⟩)
    (by simp [addCheck]) ha hp
  obtain ⟨actual, hu, hv⟩ := runtime_unary_sound hg hv guard
  exact ⟨actual, hu, extended, ha, hp, hv, he⟩

theorem binding_analysis_sound {permission : Bool}
    (wf : FlatProducts.WellTyped fs)
    (ht : FlatProducts.HasType (FlatProducts.signatures fs) context value type)
    (hc : SoundAt fs value context symbols path start first)
    (hn : start ≤ first.next)
    (hb : SoundAt fs body ((type, permission) :: context) (first.value :: first.env)
      first.normal first.next result)
    (hpop : result.env.head? = some cell) :
    SoundAt fs (if permission then .letMut value body else .letE value body) context symbols path start
      (sequence first { result with env := result.env.tail }) := by
  intro model env he hen hp valid
  have firstValid : ValidFrom start model first.checks :=
    valid_subset valid (fun _ hc => List.mem_append_left _ hc)
  have bodyValid : ValidFrom start model result.checks :=
    valid_subset valid (fun _ hc => List.mem_append_right _ hc)
  apply binding_rule (spec_frame (hc model env he hen hp firstValid) wf ht hen)
  intro value current hout
  obtain ⟨⟨middle, ha, hp, hv, he⟩, _, htyped, hvtype⟩ := hout
  have entryTyped : FlatProducts.EnvTyped (value :: current) ((type, permission) :: context) := by
    simpa only [hvtype] using FlatProducts.env_cons (v := value) (permission := permission) htyped
  apply spec_mono (hb middle (value :: current) (.cons hv he) entryTyped hp
    (valid_extend bodyValid ha hn))
  intro value final hout
  obtain ⟨extended, hext, hp, hv, he⟩ := hout
  cases hsyms : result.env with
  | nil => simp [hsyms] at hpop
  | cons symbol rest =>
    cases final with
    | nil => rw [hsyms] at he; cases he
    | cons cell final =>
      rw [hsyms] at he
      cases he with
      | cons _ he =>
        exact ⟨cell, final, rfl, extended, agree_trans ha (agree_restrict hext hn), hp, hv,
          by simpa [sequence, hsyms] using he⟩

theorem projection_analysis_sound
    (hc : SoundAt fs base context symbols path start first)
    (hg : project first.value index = some field) :
    SoundAt fs (.project base index) context symbols path start { first with value := .scalar field } := by
  intro model env he ht hp valid
  apply projection_rule
  apply spec_mono (hc model env he ht hp valid)
  intro value current hout
  obtain ⟨extended, ha, hp, hv, he⟩ := hout
  obtain ⟨actual, hproject, hactual⟩ := runtime_project_value hg hv
  exact ⟨actual, hproject, extended, ha, hp, hactual, he⟩

theorem merge_flow_checks (hg : mergeFlow condition yes no = some output) :
    output.checks = yes.checks ++ no.checks := by
  simp only [mergeFlow, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨_, _, _, _, heq⟩ := hg
  cases heq
  rfl

theorem conditional_analysis_sound
    (wf : FlatProducts.WellTyped fs)
    (ht : FlatProducts.HasType (FlatProducts.signatures fs) context condition (.scalar .bool))
    (cs : SoundAt fs condition context symbols path start first)
    (cn : start ≤ first.next) (cb : first.Bounded)
    (hb : asBoolean first.value = some test)
    (ys : SoundAt fs yes context first.env (.and first.normal (.holds test)) first.next yesResult)
    (yn : first.next ≤ yesResult.next)
    (ns : SoundAt fs no context first.env (.and first.normal (.holds (.unary .not test))) yesResult.next noResult)
    (hg : mergeFlow test yesResult noResult = some output) :
    SoundAt fs (.ifE condition yes no) context symbols path start (sequence first output) := by
  intro model env he hen hp valid
  have firstValid : ValidFrom start model first.checks :=
    valid_subset valid (fun _ hc => List.mem_append_left _ hc)
  have outputValid : ValidFrom start model output.checks :=
    valid_subset valid (fun _ hc => List.mem_append_right _ hc)
  have mergedValid : ValidFrom start model (yesResult.checks ++ noResult.checks) :=
    merge_flow_checks hg ▸ outputValid
  have testBound := as_boolean_supported hb cb.1
  apply conditional_rule (branch := fun selected current =>
    FlatProducts.EnvTyped current context ∧ ∃ middle, AgreeBelow start model middle ∧
      first.normal.Holds middle ∧ test.eval middle = some (.bool selected) ∧ RuntimeEnvRep middle first.env current)
    (by
      apply spec_mono (spec_frame (cs model env he hen hp firstValid) wf ht hen)
      intro value current hout
      obtain ⟨⟨middle, ha, hp, hv, he⟩, _, htyped, _⟩ := hout
      obtain ⟨testValue, rfl, htestValue⟩ := as_boolean_sound hb hv
      exact ⟨testValue, rfl, htyped, middle, ha, hp, htestValue, he⟩)
  intro selected current hout
  obtain ⟨htyped, middle, ha, hp, hv, he⟩ := hout
  cases selected with
  | true =>
    have childValid := valid_extend
      (valid_subset mergedValid (fun _ hc => List.mem_append_left _ hc)) ha cn
    apply spec_mono (ys middle current he htyped ⟨hp, hv⟩ childValid)
    intro value final hout
    change Covered start model output value final
    exact covered_extend (merge_flow_covered hg hv testBound hout) ha cn
  | false =>
    have childValid := valid_extend
      (valid_subset mergedValid (fun _ hc => List.mem_append_right _ hc)) ha (Nat.le_trans cn yn)
    apply spec_mono (ns middle current he htyped ⟨hp, false_guard hv⟩ childValid)
    intro value final hout
    change Covered start model output value final
    exact covered_extend (merge_flow_covered hg hv testBound (covered_extend hout agree_refl yn)) ha cn

theorem strict_short_false (h : ¬ (op = .and ∨ op = .or)) :
    FlatProducts.shortCircuit op value = false := by
  cases value with
  | tuple _ => rfl
  | scalar value => cases op <;> simp_all [FlatProducts.shortCircuit, APL.shortCircuit]

theorem strict_binary_analysis_sound
    (wf : FlatProducts.WellTyped fs)
    (ht : FlatProducts.HasType (FlatProducts.signatures fs) context left leftType)
    (ls : SoundAt fs left context symbols path start first)
    (ln : start ≤ first.next) (lb : first.Bounded)
    (rs : SoundAt fs right context first.env first.normal first.next second)
    (hg : runtimeBinary op first.value second.value = some result)
    (strict : ¬ (op = .and ∨ op = .or)) :
    SoundAt fs (.binary op left right) context symbols path start
      (sequence first (addCheck .body second.normal result.defined { second with value := result.value })) := by
  intro model env he hen hp valid
  have firstValid : ValidFrom start model first.checks :=
    valid_subset valid (fun _ hc => List.mem_append_left _ hc)
  have restValid : ValidFrom start model (second.checks ++ [⟨.body, second.normal, result.defined⟩]) :=
    valid_subset valid (fun _ hc => List.mem_append_right _ hc)
  apply binary_rule (spec_frame (ls model env he hen hp firstValid) wf ht hen)
  · intro value current _ hs
    rw [strict_short_false strict] at hs
    cases hs
  · intro value current hout hshort
    obtain ⟨⟨middle, ha, hp, hv, he⟩, _, htyped, _⟩ := hout
    have secondValid := valid_extend
      (valid_subset restValid (fun _ hc => List.mem_append_left _ hc)) ha ln
    apply spec_mono (rs middle current he htyped hp secondValid)
    intro other final hout
    obtain ⟨extended, hext, hp, ho, he⟩ := hout
    have agreement := agree_trans ha (agree_restrict hext ln)
    have guard := valid_member restValid (check := ⟨.body, second.normal, result.defined⟩)
      (by simp) agreement hp
    obtain ⟨actual, hbinary, hv⟩ := runtime_binary_sound hg (hv.agree lb.1 hext) ho hshort guard
    exact ⟨actual, hbinary, extended, agreement, hp, hv, he⟩

end APL.ProductFlow
