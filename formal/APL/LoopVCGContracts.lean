import APL.LoopVCGSoundness

/-! Typed entry-contract acceptance for the invariant generator. Requires
definedness and satisfiability retain their ordered interpretation; postconditions
refer to frozen declaration-order parameters and the returned value. No returned
value is required to exist. -/

namespace APL.LoopVCG

open VCG
open LocalState.LoopVerification

structure ContractVC where
  requiresDefined : Formula
  requiresTruth : Formula
  analysis : Analysis SymTerm
  postChecks : List Check

def postCheck (params : List SymTerm) (post : Spec) (out : Outcome SymTerm) : Option Check := do
  let term ← post.instantiate params (some out.value)
  return ⟨out.path, .and (.defined term) (.holds term)⟩

def generateContract (fs : LoopAnnotations.Functions) (calleePreconditions : Preconditions)
    (height : Nat) (types : List Ty) (body : LoopAnnotations.Term)
    (preconditions : List Spec) (post : Spec) : Option ContractVC := do
  let syms := parameterSymbols types.length
  let (defined, truth) ← requiresVC syms preconditions
  let analysis ← analyze fs calleePreconditions height (LocalState.immutable types.reverse)
    body syms.reverse truth types.length
  let postChecks ← analysis.outcomes.mapM (postCheck syms post)
  return ⟨defined, truth, analysis, postChecks⟩

def Accepted (types : List Ty) (vc : ContractVC) : Prop :=
  (∀ params : Env, params.map Val.type = types → vc.requiresDefined.Holds (modelOf params)) ∧
  (∃ params : Env, params.map Val.type = types ∧ vc.requiresTruth.Holds (modelOf params)) ∧
  (∀ params : Env, params.map Val.type = types → vc.requiresTruth.Holds (modelOf params) →
    ValidFrom types.length (modelOf params) (vc.analysis.checks ++ vc.postChecks))

theorem parameter_symbols_bounded : SymbolsBelow n (parameterSymbols n) := by
  apply symbols_of_mem
  intro symbol member
  simp only [parameterSymbols, List.mem_map] at member
  obtain ⟨i, hi, rfl⟩ := member
  exact List.mem_range.mp hi

theorem post_check_guard (hg : postCheck params post out = some check) : check.guard = out.path := by
  simp only [postCheck, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨term, _, heq⟩ := hg
  cases heq
  rfl

theorem post_check_sound {post : Spec}
    (hg : postCheck syms post out = some check)
    (hp : EnvRep model syms params) (hv : Denotes model out.value value)
    (hcheck : check.required.Holds model) :
    post.eval (params.map embed) (some (embed value)) = some (.bool true) := by
  simp only [postCheck, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨term, hterm, heq⟩ := hg
  cases heq
  exact (instantiate_sound (value := some value) hterm hp hv).symm.trans hcheck.2

theorem covered_post {post : Spec}
    (hg : analysis.outcomes.mapM (postCheck syms post) = some postChecks)
    (hp : EnvRep model syms params) (hb : SymbolsBelow bound syms)
    (hvalid : ValidFrom bound model postChecks)
    (hcovered : Covered bound model analysis value final) :
    post.eval (params.map embed) (some (embed value)) = some (.bool true) := by
  obtain ⟨out, member, extended, hmodel, hpath, hvalue, _⟩ := hcovered
  obtain ⟨check, hcheck, hmember⟩ := mapM_member hg member
  have hguard : check.guard.Holds extended := (post_check_guard hcheck).symm ▸ hpath
  have required := valid_member hvalid hmember hmodel hguard
  exact post_check_sound hcheck (env_agree hb hmodel hp) hvalue required

theorem contract_spec_sound {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (accepted : Accepted types vc) (wf : LoopAnnotations.WellTyped fs)
    (hbody : LoopAnnotations.HasType (LoopAnnotations.signatures fs)
      (LocalState.immutable types.reverse) body resultTy)
    (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions) :
    EvalSpec (LoopAnnotations.eraseFunctions fs) body.erase params.reverse
      (fun value _ => value.type = resultTy ∧
        post.eval (params.map embed) (some (embed value)) = some (.bool true)) := by
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, analysis, hanalyze, postChecks, hposts, heq⟩ := hgen
  cases heq
  have parameterRep := typed_parameters_rep ht
  have pathTrue := (requires_vc_sound hrequires parameterRep).2.mpr hpre
  have allValid := accepted.2.2 params ht pathTrue
  have bodyValid := valid_subset allValid (fun check member => List.mem_append_left _ member)
  have postValid := valid_subset allValid (fun check member => List.mem_append_right _ member)
  have envTyped : LocalState.EnvTyped params.reverse (LocalState.immutable types.reverse) := by
    simp [LocalState.EnvTyped, LocalState.immutable, List.map_reverse, List.map_map, Function.comp_def, ht]
  have bodyTyped : LocalState.HasType (LocalState.signatures (LoopAnnotations.eraseFunctions fs))
      (LocalState.immutable types.reverse) body.erase resultTy := by
    rw [LoopAnnotations.erase_signatures]
    exact LoopAnnotations.erase_typed hbody
  have wfErased := LoopAnnotations.erase_wellTyped wf
  have semantic := LoopVCG.analyze_sound wfErased hanalyze
    (symbols_reverse parameter_symbols_bounded) (requires_bounded hrequires parameter_symbols_bounded).2
    (modelOf params) params.reverse (env_reverse parameterRep) envTyped pathTrue bodyValid
  apply spec_mono (spec_frame semantic wfErased bodyTyped envTyped)
  intro value final hnormal
  exact ⟨hnormal.2.2.2,
    covered_post hposts parameterRep parameter_symbols_bounded postValid hnormal.1⟩

theorem contract_run_sound {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (accepted : Accepted types vc) (wf : LoopAnnotations.WellTyped fs)
    (hbody : LoopAnnotations.HasType (LoopAnnotations.signatures fs)
      (LocalState.immutable types.reverse) body resultTy)
    (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions) :
    StateVCG.RunSafe (fun value _ => value.type = resultTy ∧
      post.eval (params.map embed) (some (embed value)) = some (.bool true))
      (LocalState.run (LoopAnnotations.eraseFunctions fs) budget (.eval body.erase params.reverse [])) :=
  closed_run (contract_spec_sound hgen accepted wf hbody ht hpre)

theorem contract_steps_value {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (accepted : Accepted types vc) (wf : LoopAnnotations.WellTyped fs)
    (hbody : LoopAnnotations.HasType (LoopAnnotations.signatures fs)
      (LocalState.immutable types.reverse) body resultTy)
    (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions)
    (trace : LocalState.Steps (LoopAnnotations.eraseFunctions fs)
      (.eval body.erase params.reverse []) (.ret value final [])) :
    value.type = resultTy ∧ post.eval (params.map embed) (some (embed value)) = some (.bool true) := by
  obtain ⟨budget, hr⟩ := LocalState.run_complete trace rfl
  have safe := contract_run_sound (budget := budget) hgen accepted wf hbody ht hpre
  simpa only [hr, StateVCG.RunSafe] using safe

theorem contract_steps_no_trap {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (accepted : Accepted types vc) (wf : LoopAnnotations.WellTyped fs)
    (hbody : LoopAnnotations.HasType (LoopAnnotations.signatures fs)
      (LocalState.immutable types.reverse) body resultTy)
    (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions) :
    ¬ LocalState.Steps (LoopAnnotations.eraseFunctions fs) (.eval body.erase params.reverse []) (.trap kind) :=
  no_finite_trap (contract_spec_sound hgen accepted wf hbody ht hpre)

theorem contract_steps_no_invalid {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (accepted : Accepted types vc) (wf : LoopAnnotations.WellTyped fs)
    (hbody : LoopAnnotations.HasType (LoopAnnotations.signatures fs)
      (LocalState.immutable types.reverse) body resultTy)
    (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions) :
    ¬ LocalState.Steps (LoopAnnotations.eraseFunctions fs) (.eval body.erase params.reverse []) .invalid :=
  no_finite_invalid (contract_spec_sound hgen accepted wf hbody ht hpre)

theorem contract_preconditions_defined {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (accepted : Accepted types vc) (ht : params.map Val.type = types) :
    RequiresDefined (params.map embed) preconditions := by
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, analysis, _, postChecks, _, heq⟩ := hgen
  cases heq
  exact (requires_vc_sound hrequires (typed_parameters_rep ht)).1.mp (accepted.1 params ht)

theorem contract_nonvacuous
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (accepted : Accepted types vc) :
    ∃ params : Env, params.map Val.type = types ∧ RequiresHold (params.map embed) preconditions := by
  obtain ⟨params, ht, pathTrue⟩ := accepted.2.1
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, analysis, _, postChecks, _, heq⟩ := hgen
  cases heq
  exact ⟨params, ht, (requires_vc_sound hrequires (typed_parameters_rep ht)).2.mp pathTrue⟩

end APL.LoopVCG
