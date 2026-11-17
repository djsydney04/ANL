import APL.ProductQueries
import APL.ProductEntry

namespace APL.ProductFlow
open ProductLogic ProductAnnotations ProductEntry
open FlatProducts.LoopVerification

structure ContractOutput where
  entry : EntryChecks
  body : Analysis SymValue
  posts : List Check

def ContractOutput.checks (output : ContractOutput) : List Check :=
  output.entry.checks ++ output.body.checks ++ output.posts

def generateContract (fs : ProductAnnotations.Functions) (height : Nat)
    (fn : ProductAnnotations.Function) : Option ContractOutput := do
  let params := parameterLayout fn.params 0
  let entry ← entryChecks params fn.requires (envDomain params) 0
  let body ← analyze fs height (FlatProducts.immutable fn.params.reverse) fn.body params.reverse
    entry.path (reservedCount fn.params) []
  let posts ← postChecks params body.value body.normal fn.ensures 0
  return ⟨entry, body, posts⟩

def ContractOutput.Accepted (output : ContractOutput) : Prop :=
  (∀ model, NamedQueriesHold model (groupChecks output.checks)) ∧
    ∃ model, output.entry.path.Holds model

theorem contract_eval_sound
    (wf : FlatProducts.WellTyped (eraseFunctions fs))
    (hg : generateContract fs height fn = some output)
    (hr : RuntimeEnvRep model (parameterLayout fn.params 0) params)
    (hp : RequiresHold (params.map embedValue) fn.requires)
    (valid : ValidFrom (reservedCount fn.params) model output.checks) :
    EvalSpec (eraseFunctions fs) fn.body.erase params.reverse
      (fun value final => Covered (reservedCount fn.params) model output.body value final ∧
        AssertionsHold (params.map embedValue) (some (embedValue value)) [] fn.ensures) := by
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨entry, he, body, hb, posts, hposts, heq⟩ := hg
  cases heq
  have initialBound := parameter_initial_support (types := fn.params)
  have pathBound := entry_checks_supported he initialBound (env_domain_supported initialBound)
  have bodyValid : ValidFrom (reservedCount fn.params) model body.checks :=
    valid_subset valid (fun _ hc => List.mem_append_left _ (List.mem_append_right _ hc))
  have postValid : ValidFrom (reservedCount fn.params) model posts :=
    valid_subset valid (fun _ hc => List.mem_append_right _ hc)
  have path := (entry_checks_sound he hr).2.mpr ⟨env_domain_sound hr, hp⟩
  obtain ⟨bodyRep, bodyTyped⟩ := parameter_body_entry hr
  apply spec_mono (analyze_sound wf hb (symbols_reverse initialBound) pathBound
    model params.reverse bodyRep bodyTyped path bodyValid)
  intro value final covered
  refine ⟨covered, ?_⟩
  obtain ⟨extended, ha, hnormal, hv, _⟩ := covered
  have frozenParams : RuntimeEnvRep extended (parameterLayout fn.params 0) params := hr.agree initialBound ha
  exact (post_checks_sound hposts frozenParams hv).mp (postValid extended ha) hnormal

theorem contract_requires_defined
    (hg : generateContract fs height fn = some output)
    (hr : RuntimeEnvRep model (parameterLayout fn.params 0) params)
    (valid : (group output.checks).Holds model) :
    RequiresDefined (params.map embedValue) fn.requires := by
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨entry, he, body, _, posts, _, heq⟩ := hg
  cases heq
  have entryValid : (group entry.checks).Holds model := by
    apply group_exact.mpr
    intro check hc
    exact group_exact.mp valid check (List.mem_append_left _ (List.mem_append_left _ hc))
  exact (entry_checks_sound he hr).1.mp entryValid (env_domain_sound hr)

theorem contract_reachable_iff
    (hg : generateContract fs height fn = some output) :
    (∃ model, output.entry.path.Holds model) ↔
      ∃ params : FlatProducts.Env, params.map FlatProducts.Val.type = fn.params ∧
        RequiresHold (params.map embedValue) fn.requires := by
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨entry, he, body, _, posts, _, heq⟩ := hg
  cases heq
  constructor
  · rintro ⟨model, hp⟩
    have domain := entry_path_input he hp
    obtain ⟨params, ht, hr⟩ := parameter_entry_complete domain
    exact ⟨params, ht, ((entry_checks_sound he hr).2.mp hp).2⟩
  · rintro ⟨params, ht, hp⟩
    obtain ⟨model, hr, hd⟩ := parameter_entry_exists ht
    exact ⟨model, (entry_checks_sound he hr).2.mpr ⟨hd, hp⟩⟩

theorem contract_accepted_eval
    (wf : ProductAnnotations.WellTyped fs)
    (hg : generateContract fs height fn = some output)
    (ht : params.map FlatProducts.Val.type = fn.params)
    (hp : RequiresHold (params.map embedValue) fn.requires)
    (accepted : output.Accepted) :
    EvalSpec (eraseFunctions fs) fn.body.erase params.reverse
      (fun value final => Covered (reservedCount fn.params) (parameterModel params) output.body value final ∧
        AssertionsHold (params.map embedValue) (some (embedValue value)) [] fn.ensures) := by
  apply contract_eval_sound (erase_wellTyped wf) hg (parameter_model_rep ht) hp
  intro extended _
  exact named_queries_exact.mp (accepted.1 extended)

theorem contract_accepted_run
    (wf : ProductAnnotations.WellTyped fs)
    (hg : generateContract fs height fn = some output)
    (ht : params.map FlatProducts.Val.type = fn.params)
    (hp : RequiresHold (params.map embedValue) fn.requires)
    (accepted : output.Accepted) :
    RunSafe (fun value final => Covered (reservedCount fn.params) (parameterModel params) output.body value final ∧
      AssertionsHold (params.map embedValue) (some (embedValue value)) [] fn.ensures)
      (FlatProducts.run (eraseFunctions fs) budget (.eval fn.body.erase params.reverse [])) :=
  closed_run (contract_accepted_eval wf hg ht hp accepted)

theorem contract_accepted_nonvacuous
    (hg : generateContract fs height fn = some output) (accepted : output.Accepted) :
    ∃ params : FlatProducts.Env, params.map FlatProducts.Val.type = fn.params ∧
      RequiresHold (params.map embedValue) fn.requires :=
  (contract_reachable_iff hg).mp accepted.2

theorem root_contract_sound {function : Nat} {params : FlatProducts.Env}
    (wf : ProductAnnotations.WellTyped fs)
    (hf : fs[function]? = some fn)
    (hg : generateContract fs height fn = some output)
    (ht : params.map FlatProducts.Val.type = fn.params)
    (hp : RequiresHold (params.map embedValue) fn.requires)
    (accepted : output.Accepted) :
    EvalSpec (eraseFunctions fs) fn.body.erase params.reverse
      (fun value final =>
        (Covered (reservedCount fn.params) (parameterModel params) output.body value final ∧
          AssertionsHold (params.map embedValue) (some (embedValue value)) [] fn.ensures) ∧
        FlatProducts.Frozen (FlatProducts.immutable fn.params.reverse) params.reverse final ∧
        FlatProducts.EnvTyped final (FlatProducts.immutable fn.params.reverse) ∧ value.type = fn.result) := by
  apply spec_frame (contract_accepted_eval wf hg ht hp accepted) (erase_wellTyped wf)
  · rw [erase_signatures]
    exact erase_typed (wf function fn hf).1
  · exact (parameter_body_entry (parameter_model_rep ht)).2

theorem contract_accepted_no_finite_trap {params : FlatProducts.Env}
    (wf : ProductAnnotations.WellTyped fs)
    (hg : generateContract fs height fn = some output)
    (ht : params.map FlatProducts.Val.type = fn.params)
    (hp : RequiresHold (params.map embedValue) fn.requires)
    (accepted : output.Accepted) :
    ¬ FlatProducts.Steps (eraseFunctions fs) (.eval fn.body.erase params.reverse []) (.trap kind) :=
  no_finite_trap (contract_accepted_eval wf hg ht hp accepted)

theorem contract_accepted_no_finite_invalid {params : FlatProducts.Env}
    (wf : ProductAnnotations.WellTyped fs)
    (hg : generateContract fs height fn = some output)
    (ht : params.map FlatProducts.Val.type = fn.params)
    (hp : RequiresHold (params.map embedValue) fn.requires)
    (accepted : output.Accepted) :
    ¬ FlatProducts.Steps (eraseFunctions fs) (.eval fn.body.erase params.reverse []) .invalid :=
  no_finite_invalid (contract_accepted_eval wf hg ht hp accepted)

theorem contract_accepted_normal
    (wf : ProductAnnotations.WellTyped fs)
    (hg : generateContract fs height fn = some output)
    (ht : params.map FlatProducts.Val.type = fn.params)
    (hp : RequiresHold (params.map embedValue) fn.requires)
    (accepted : output.Accepted)
    (trace : FlatProducts.Steps (eraseFunctions fs) (.eval fn.body.erase params.reverse []) (.ret value final [])) :
    Covered (reservedCount fn.params) (parameterModel params) output.body value final ∧
      AssertionsHold (params.map embedValue) (some (embedValue value)) [] fn.ensures :=
  normal_result (contract_accepted_eval wf hg ht hp accepted) trace

theorem contract_accepted_entry_defined {params : FlatProducts.Env}
    (hg : generateContract fs height fn = some output)
    (ht : params.map FlatProducts.Val.type = fn.params)
    (accepted : output.Accepted) : RequiresDefined (params.map embedValue) fn.requires :=
  contract_requires_defined hg (parameter_model_rep ht)
    (named_queries_exact.mp (accepted.1 (parameterModel params)))

end APL.ProductFlow
