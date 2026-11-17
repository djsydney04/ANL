import APL.ProductFlowBoolean

namespace APL.ProductFlow
open ProductLogic
open FlatProducts.LoopVerification

theorem call_analysis_sound
    (argsSpec : ∀ model env, RuntimeEnvRep model symbols env → FlatProducts.EnvTyped env context →
      path.Holds model → ValidFrom start model actuals.checks →
      ArgsSpec (ProductAnnotations.eraseFunctions fs) args env (ArgsCovered start model actuals))
    (an : start ≤ actuals.next) (ab : actuals.ArgsBounded)
    (hf : fs[function]? = some fn)
    (ht : actuals.value.map SymValue.type = fn.params)
    (bs : SoundAt (ProductAnnotations.eraseFunctions fs) fn.body.erase
      (FlatProducts.immutable fn.params.reverse) actuals.value.reverse actuals.normal actuals.next bodyResult) :
    SoundAt (ProductAnnotations.eraseFunctions fs) (.call function args) context symbols path start
      (sequence actuals (addCheck .body actuals.normal required { bodyResult with env := actuals.env })) := by
  intro model env he hen hp valid
  have argumentValid : ValidFrom start model actuals.checks :=
    valid_subset valid (fun _ hc => List.mem_append_left _ hc)
  have bodyValid : ValidFrom start model bodyResult.checks :=
    valid_subset valid (fun _ hc => List.mem_append_right _ (List.mem_append_left _ hc))
  apply call_rule
  apply args_spec_mono (argsSpec model env he hen hp argumentValid)
  intro values caller hout
  obtain ⟨middle, ha, hp, hv, he⟩ := hout
  have typed : FlatProducts.EnvTyped values.reverse (FlatProducts.immutable fn.params.reverse) := by
    have htypes := (runtime_env_types hv).symm.trans ht
    simpa [FlatProducts.EnvTyped, FlatProducts.immutable, List.map_reverse, List.map_map, Function.comp_def] using
      congrArg List.reverse htypes
  refine ⟨fn.erase, ProductAnnotations.erase_lookup hf, ?_⟩
  apply spec_mono (bs middle values.reverse (by simpa [RuntimeEnvRep, List.map_reverse] using hv.reverse) typed hp (valid_extend bodyValid ha an))
  intro value _ hout
  obtain ⟨extended, hext, hp, hv, _⟩ := hout
  exact ⟨extended, agree_trans ha (agree_restrict hext an), hp, hv, he.agree ab.2.1 hext⟩

theorem tuple_analysis_sound {types : List APL.Ty}
    (wf : FlatProducts.WellTyped fs)
    (ht : FlatProducts.ArgsTyped (FlatProducts.signatures fs) context fields (types.map FlatProducts.Ty.scalar))
    (argsSpec : ∀ model env, RuntimeEnvRep model symbols env → FlatProducts.EnvTyped env context →
      path.Holds model → ValidFrom start model captured.checks → ArgsSpec fs fields env (ArgsCovered start model captured))
    (hg : tupleSymbol captured.value = some value) :
    SoundAt fs (.tuple fields) context symbols path start { captured with value := value } := by
  intro model env he hen hp valid
  apply tuple_rule
  apply fields_spec_mono (args_fields_spec wf ht hen (argsSpec model env he hen hp valid))
  intro values final hout
  obtain ⟨extended, ha, hp, hv, he⟩ := hout
  obtain ⟨actual, hc, hv⟩ := runtime_tuple_value hg hv
  exact ⟨actual, hc, extended, ha, hp, hv, he⟩

end APL.ProductFlow
