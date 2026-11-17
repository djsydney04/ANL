import APL.StateVCG
import APL.LocalStateSafety

namespace APL.StateVCG
open VCG

/-- Specifications use frozen declaration-order parameters, even after local mutation. -/
def generateContract (fs : LocalState.Functions) (calleePreconditions : Preconditions) (height : Nat)
    (types : List Ty) (body : LocalState.Term) (preconditions : List Spec) (post : Spec) :
    Option ContractVC := do
  let syms := parameterSymbols types.length
  let (defined, truth) ← requiresVC syms preconditions
  let formula ← wp fs calleePreconditions height body syms.reverse (fun value _ => specPost syms post value)
  return ⟨defined, truth, formula⟩

private theorem contract_trace {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map VCG.embed) preconditions) :
    ∃ v finalEnv,
      LocalState.Steps fs (.eval body params.reverse []) (.ret v finalEnv []) ∧
      post.eval (params.map VCG.embed) (some (VCG.embed v)) = some (.bool true) := by
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, formula, hwp, hgen⟩ := hgen
  cases hgen
  have hp := typed_parameters_rep ht
  have htruth := ((requires_vc_sound hrequires hp).2).mpr hpre
  have hvalid := ha.2.2 params ht htruth
  obtain ⟨v, finalEnv, trace, result, _, q, hq, hqvalid, hd, _⟩ :=
    wp_trace (k := []) hwp (env_reverse hp) hvalid
  exact ⟨v, finalEnv, trace, spec_post_sound ⟨result, q, hq, hqvalid, hd⟩ hp⟩

private theorem contract_value_typed {params : Env}
    (wf : LocalState.WellTyped fs)
    (hb : LocalState.HasType (LocalState.signatures fs) (LocalState.immutable types.reverse) body resultTy)
    (ht : params.map Val.type = types)
    (trace : LocalState.Steps fs (.eval body params.reverse []) (.ret v finalEnv [])) :
    v.type = resultTy := by
  have envTyped : LocalState.EnvTyped params.reverse (LocalState.immutable types.reverse) := by
    simp [LocalState.EnvTyped, LocalState.immutable, List.map_reverse, List.map_map, Function.comp_def, ht]
  have initial := LocalState.State.Typed.eval hb envTyped LocalState.KontTyped.nil
  have last := LocalState.steps_preserve wf initial trace
  cases last with
  | ret _ hk => cases hk; rfl

theorem contract_run_sound {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (wf : LocalState.WellTyped fs)
    (hb : LocalState.HasType (LocalState.signatures fs) (LocalState.immutable types.reverse) body resultTy)
    (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map VCG.embed) preconditions) :
    RunSafe (fun v _ => v.type = resultTy ∧
      post.eval (params.map VCG.embed) (some (VCG.embed v)) = some (.bool true))
      (LocalState.run fs fuel (.eval body params.reverse [])) := by
  obtain ⟨v, finalEnv, trace, hp⟩ := contract_trace hgen ha ht hpre
  have hv := contract_value_typed wf hb ht trace
  cases hr : LocalState.run fs fuel (.eval body params.reverse []) with
  | none => trivial
  | some last =>
    have same := run_result trace hr
    subst last
    exact ⟨hv, hp⟩

theorem contract_run_complete {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (wf : LocalState.WellTyped fs)
    (hb : LocalState.HasType (LocalState.signatures fs) (LocalState.immutable types.reverse) body resultTy)
    (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map VCG.embed) preconditions) :
    ∃ fuel v finalEnv,
      LocalState.run fs fuel (.eval body params.reverse []) = some (.ret v finalEnv []) ∧
      v.type = resultTy ∧ post.eval (params.map VCG.embed) (some (VCG.embed v)) = some (.bool true) := by
  obtain ⟨v, finalEnv, trace, hp⟩ := contract_trace hgen ha ht hpre
  obtain ⟨fuel, hr⟩ := LocalState.run_complete trace rfl
  exact ⟨fuel, v, finalEnv, hr, contract_value_typed wf hb ht trace, hp⟩

theorem contract_steps_value {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (wf : LocalState.WellTyped fs)
    (hb : LocalState.HasType (LocalState.signatures fs) (LocalState.immutable types.reverse) body resultTy)
    (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map VCG.embed) preconditions)
    (trace : LocalState.Steps fs (.eval body params.reverse []) (.ret v finalEnv [])) :
    v.type = resultTy ∧ post.eval (params.map VCG.embed) (some (VCG.embed v)) = some (.bool true) := by
  obtain ⟨fuel, hr⟩ := LocalState.run_complete trace rfl
  have hs := contract_run_sound (fuel := fuel) hgen ha wf hb ht hpre
  simpa only [hr, RunSafe] using hs

theorem contract_steps_no_trap {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (wf : LocalState.WellTyped fs)
    (hb : LocalState.HasType (LocalState.signatures fs) (LocalState.immutable types.reverse) body resultTy)
    (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map VCG.embed) preconditions) :
    ¬ LocalState.Steps fs (.eval body params.reverse []) (.trap kind) := by
  intro trace
  obtain ⟨fuel, hr⟩ := LocalState.run_complete trace rfl
  have hs := contract_run_sound (fuel := fuel) hgen ha wf hb ht hpre
  simp only [hr, RunSafe] at hs

theorem contract_steps_no_invalid {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (wf : LocalState.WellTyped fs)
    (hb : LocalState.HasType (LocalState.signatures fs) (LocalState.immutable types.reverse) body resultTy)
    (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map VCG.embed) preconditions) :
    ¬ LocalState.Steps fs (.eval body params.reverse []) .invalid := by
  intro trace
  obtain ⟨fuel, hr⟩ := LocalState.run_complete trace rfl
  have hs := contract_run_sound (fuel := fuel) hgen ha wf hb ht hpre
  simp only [hr, RunSafe] at hs

theorem contract_preconditions_defined {params : Env}
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types) :
    RequiresDefined (params.map VCG.embed) preconditions := by
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, formula, _, hgen⟩ := hgen
  cases hgen
  exact ((requires_vc_sound hrequires (typed_parameters_rep ht)).1).mp (ha.1 params ht)

theorem contract_nonvacuous
    (hgen : generateContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) :
    ∃ params : Env, params.map Val.type = types ∧ RequiresHold (params.map VCG.embed) preconditions := by
  obtain ⟨params, ht, htruth⟩ := ha.2.1
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, formula, _, hgen⟩ := hgen
  cases hgen
  exact ⟨params, ht, ((requires_vc_sound hrequires (typed_parameters_rep ht)).2).mp htruth⟩

end APL.StateVCG
