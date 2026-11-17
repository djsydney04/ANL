import APL.ProductFlowSemantics

namespace APL.ProductFlow
open ProductLogic ProductAnnotations
open VCG (Model)
open FlatProducts.LoopVerification

theorem invariant_checks_established
    (hg : (group (invariantChecks site isPreservation path clauses)).Holds model)
    (hp : path.Holds model) : (clauseConjunction clauses).Holds model := by
  have every : ∀ clause ∈ clauses, clause.truth.Holds model := by
    intro clause hc
    obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp hc
    apply group_exact.mp hg ⟨.invariant site isPreservation index, path, clause.truth⟩ _ hp
    exact List.mem_map.mpr ⟨(clause, index), List.mk_mem_zipIdx_iff_getElem?.mpr hi, rfl⟩
  clear hg
  induction clauses with
  | nil => trivial
  | cons clause clauses ih =>
    exact ⟨every clause (.head _), ih (fun other ho => every other (.tail _ ho))⟩

theorem false_guard (h : term.eval model = some (.bool false)) :
    (Formula.holds (.unary .not term)).Holds model := by
  simp [Formula.Holds, SymTerm.eval, h, VCG.mUnary]

theorem loop_analysis_sound
    (wf : FlatProducts.WellTyped fs)
    (htc : FlatProducts.HasType (FlatProducts.signatures fs) context condition (.scalar .bool))
    (htb : FlatProducts.HasType (FlatProducts.signatures fs) context body (.scalar .unit))
    (hs : SymbolsBelow start symbols) (hpath : path.Supported start)
    (hi : assertionsVC [] none symbols clauses = some initial)
    (hh : freshHead context symbols start = some head)
    (hinv : assertionsVC [] none head.symbols clauses = some invariant)
    (cs : SoundAt fs condition context head.symbols
      (.and path (.and head.domain (clauseConjunction invariant))) head.next conditionResult)
    (cn : head.next ≤ conditionResult.next)
    (htest : asBoolean conditionResult.value = some test)
    (bs : SoundAt fs body context conditionResult.env
      (.and conditionResult.normal (.holds test)) conditionResult.next bodyResult)
    (hpres : assertionsVC [] none bodyResult.env clauses = some preservedClauses) :
    SoundAt fs (.whileE condition body) context symbols path start
      ⟨runtimeLiteral (.scalar .unit), conditionResult.env,
        .and conditionResult.normal (.holds (.unary .not test)),
        invariantChecks site false path initial ++ conditionResult.checks ++ bodyResult.checks ++
          invariantChecks site true bodyResult.normal preservedClauses, bodyResult.next⟩ := by
  intro model entry hentry entryTyped entryPath accepted
  have hn := (fresh_head_bounded hh hs).1
  have htotal := Nat.le_trans hn cn
  have initialValid : ValidFrom start model (invariantChecks site false path initial) :=
    valid_subset accepted (fun check hc => by simp only [List.mem_append]; exact .inl (.inl (.inl hc)))
  have conditionValid : ValidFrom start model conditionResult.checks :=
    valid_subset accepted (fun check hc => by simp only [List.mem_append]; exact .inl (.inl (.inr hc)))
  have bodyValid : ValidFrom start model bodyResult.checks :=
    valid_subset accepted (fun check hc => by simp only [List.mem_append]; exact .inl (.inr hc))
  have preservationValid : ValidFrom start model
      (invariantChecks site true bodyResult.normal preservedClauses) :=
    valid_subset accepted (fun check hc => by simp only [List.mem_append]; exact .inr hc)
  let I : FlatProducts.Env → Prop := fun current => FlatProducts.Frozen context entry current ∧
    FlatProducts.EnvTyped current context ∧ AssertionsHold [] none (current.map embedValue) clauses
  let G : Bool → FlatProducts.Env → Prop := fun value current =>
    FlatProducts.Frozen context entry current ∧ FlatProducts.EnvTyped current context ∧
    ∃ extended, AgreeBelow start model extended ∧ conditionResult.normal.Holds extended ∧
      test.eval extended = some (.bool value) ∧ RuntimeEnvRep extended conditionResult.env current
  have initialInvariant : I entry := by
    refine ⟨FlatProducts.frozen_refl entryTyped, entryTyped, ?_⟩
    apply (assertions_vc_sound (result := none) hi .nil trivial hentry).mp
    exact invariant_checks_established (initialValid model agree_refl) entryPath
  have conditionSpec : ∀ current, I current → EvalSpec fs condition current
      (fun value final => ∃ test, value = .scalar (.bool test) ∧ G test final) := by
    intro current hI
    obtain ⟨frozen, typed, established⟩ := hI
    obtain ⟨_, _, extended, ha, hhead, hdomain⟩ := fresh_head_coverage hh hs hentry frozen typed
    have headInvariant := (assertions_vc_sound (result := none) hinv .nil trivial hhead).mpr established
    have headPath := (path.holds_agree hpath ha).mp entryPath
    apply spec_mono (spec_frame
      (cs extended current hhead typed ⟨headPath, hdomain, headInvariant⟩
        (valid_extend conditionValid ha hn)) wf htc typed)
    intro value final hout
    obtain ⟨⟨lastModel, hext, hp, hv, he⟩, frame, finalTyped, _⟩ := hout
    obtain ⟨value, rfl, hvalue⟩ := as_boolean_sound htest hv
    exact ⟨value, rfl, FlatProducts.frozen_trans frozen frame, finalTyped, lastModel,
      agree_trans ha (agree_restrict hext hn), hp, hvalue, he⟩
  have bodySpec : ∀ current, G true current → EvalSpec fs body current
      (fun value final => value = .scalar .unit ∧ I final) := by
    intro current hG
    obtain ⟨frozen, typed, currentModel, ha, hp, hv, he⟩ := hG
    apply spec_mono (spec_frame
      (bs currentModel current he typed ⟨hp, hv⟩ (valid_extend bodyValid ha htotal)) wf htb typed)
    intro value final hout
    obtain ⟨⟨lastModel, hext, hp, _, he⟩, frame, finalTyped, valueTyped⟩ := hout
    have agreement := agree_trans ha (agree_restrict hext htotal)
    have inv : AssertionsHold [] none (final.map embedValue) clauses := by
      apply (assertions_vc_sound (result := none) hpres .nil trivial he).mp
      exact invariant_checks_established (preservationValid lastModel agreement) hp
    obtain ⟨scalar, rfl, hscalar⟩ := FlatProducts.scalar_canonical valueTyped
    cases scalar with
    | int _ | bool _ => cases hscalar
    | unit => exact ⟨rfl, FlatProducts.frozen_trans frozen frame, finalTyped, inv⟩
  apply spec_mono (invariant_loop_rule conditionSpec bodySpec initialInvariant)
  intro value final hout
  obtain ⟨rfl, _, _, finalModel, ha, hp, hv, he⟩ := hout
  exact ⟨finalModel, ha, ⟨hp, false_guard hv⟩, runtime_literal_denotes (value := .scalar .unit), he⟩

end APL.ProductFlow
