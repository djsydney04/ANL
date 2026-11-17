import APL.LoopGenerationRank

/-! A sufficient finite height for the unchanged invariant analyzer, from
verification-ready typing, typed preconditions, complete supplied call-rank
coverage and symbolic environment length. Runtime loops may diverge. -/

namespace APL.LoopGeneration
open VCG LoopVCG LoopAnnotations

private theorem signatures_entry {fs : Functions} {f : Nat} {params : List Ty} {result : Ty} (h : (signatures fs)[f]? = some (params, result)) :
    ∃ fn : Function, fs[f]? = some fn ∧ fn.params = params ∧ fn.result = result := by
  simp only [signatures, Array.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨fn, hf, hp⟩ := h
  exact ⟨fn, hf, (Prod.mk.inj hp).1, (Prod.mk.inj hp).2⟩

private theorem args_member_type (ht : ArgsTyped sigs Γ args types) (hm : arg ∈ args) :
    ∃ ty, LoopAnnotations.HasType sigs Γ arg ty := by
  induction args generalizing types with
  | nil => cases hm
  | cons a rest ih =>
    cases ht with
    | cons ha hb =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨_, ha⟩
      · exact ih hb hm

private theorem args_length (ht : ArgsTyped sigs Γ args types) : args.length = types.length := by
  induction args generalizing types with
  | nil => cases ht; rfl
  | cons a rest ih =>
    cases ht with
    | cons ha hb => simp [ih hb]

/-- A purely structural sufficient-height theorem for the unchanged analyzer.
No logical validity, symbolic denotation, reachability, or runtime safety premise. -/
theorem analyze_complete
    (wf : WellTyped fs) (hp : PreconditionsTyped fs preconditions) (ranked : Ranked fs rank)
    (ht : LoopAnnotations.HasType (signatures fs) Γ e ty) (hr : CallsBelow rank ceiling e)
    (hlen : env.length = Γ.length)
    (heightBound : ceiling * bodyBound fs + nodes e < height) :
    ∃ generated, analyze fs preconditions height Γ e env path start = some generated ∧
      Shape Γ.length generated := by
  induction height generalizing Γ e ty ceiling env path start with
  | zero => omega
  | succ height ih =>
    have inferred := LocalState.infer_complete (erase_typed ht)
    simp only [analyze, inferred, bind, Option.bind_some]
    cases ht with
    | lit => exact ⟨_, rfl, shape_single hlen⟩
    | «local» hi =>
      have bound := (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨symbol, hs⟩ := lookup_exists (hlen ▸ bound)
      exact ⟨single symbol env path start, by simp [hs], shape_single hlen⟩
    | @unary Γ a op ha =>
      have small : ceiling * bodyBound fs + nodes a < height := by
        simp only [nodes] at heightBound
        omega
      obtain ⟨argument, hg, hs⟩ := ih (path := path) (start := start) ha hr hlen small
      simp only [hg, Option.bind_some]
      apply bind_total
      intro out member next
      exact ⟨addCheck out.path (unaryGuard op out.value)
        (single (.unary op out.value) out.env out.path next), rfl, shape_single (next := next) (hs out member)⟩
    | @assign Γ i t a hi ha =>
      have small : ceiling * bodyBound fs + nodes a < height := by
        simp only [nodes] at heightBound
        omega
      obtain ⟨value, hg, hs⟩ := ih (path := path) (start := start) ha hr hlen small
      simp only [hg, Option.bind_some]
      apply bind_total
      intro out member next
      have index := (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨updated, hu, hl⟩ := update_total (value := out.value) ((hs out member) ▸ index)
      exact ⟨single (.lit .unit) updated out.path next, by simp [hu], shape_single (hl.trans (hs out member))⟩
    | @letE Γ a u b t ha hb =>
      have smallA : ceiling * bodyBound fs + nodes a < height := by simp only [nodes] at heightBound; omega
      have smallB : ceiling * bodyBound fs + nodes b < height := by simp only [nodes] at heightBound; omega
      obtain ⟨first, hf, hs⟩ := ih (path := path) (start := start) ha hr.1 hlen smallA
      have inferA := LocalState.infer_complete (erase_typed ha)
      simp only [inferA, hf, Option.bind_some]
      apply bind_total
      intro out member next
      obtain ⟨body, hg, hbody⟩ := ih (env := out.value :: out.env) (path := out.path) (start := next) hb hr.2 (by simpa using congrArg Nat.succ (hs out member)) smallB
      obtain ⟨results, hpop, hpopped⟩ := pop_total hbody
      simp only [bind, Option.pure_def] at hpop
      exact ⟨{ body with outcomes := results }, by simp [hg, hpop], hpopped⟩
    | @letMut Γ a u b t ha hb =>
      have smallA : ceiling * bodyBound fs + nodes a < height := by simp only [nodes] at heightBound; omega
      have smallB : ceiling * bodyBound fs + nodes b < height := by simp only [nodes] at heightBound; omega
      obtain ⟨first, hf, hs⟩ := ih (path := path) (start := start) ha hr.1 hlen smallA
      have inferA := LocalState.infer_complete (erase_typed ha)
      simp only [inferA, hf, Option.bind_some]
      apply bind_total
      intro out member next
      obtain ⟨body, hg, hbody⟩ := ih (env := out.value :: out.env) (path := out.path) (start := next) hb hr.2 (by simpa using congrArg Nat.succ (hs out member)) smallB
      obtain ⟨results, hpop, hpopped⟩ := pop_total hbody
      simp only [bind, Option.pure_def] at hpop
      exact ⟨{ body with outcomes := results }, by simp [hg, hpop], hpopped⟩
    | @ifE Γ condition yes t no hc ha hb =>
      have sc : ceiling * bodyBound fs + nodes condition < height := by simp only [nodes] at heightBound; omega
      have sa : ceiling * bodyBound fs + nodes yes < height := by simp only [nodes] at heightBound; omega
      have sb : ceiling * bodyBound fs + nodes no < height := by simp only [nodes] at heightBound; omega
      obtain ⟨test, ht, hs⟩ := ih (path := path) (start := start) hc hr.1 hlen sc
      simp only [ht, Option.bind_some]
      apply bind_total
      intro out member next
      obtain ⟨a, ha, hsa⟩ := ih (path := .and out.path (.holds out.value)) (start := next)
        ha hr.2.1 (hs out member) sa
      obtain ⟨b, hb, hsb⟩ := ih (path := .and out.path (.holds (.unary .not out.value))) (start := a.next)
        hb hr.2.2 (hs out member) sb
      exact ⟨addCheck out.path (.boolean out.value) (combine a b), by simp [ha, hb], shape_combine hsa hsb⟩
    | @binary Γ left u right v op t hl hrhs hop =>
      have sl : ceiling * bodyBound fs + nodes left < height := by simp only [nodes] at heightBound; omega
      have sr : ceiling * bodyBound fs + nodes right < height := by simp only [nodes] at heightBound; omega
      obtain ⟨lhs, hg, hs⟩ := ih (path := path) (start := start) hl hr.1 hlen sl
      simp only [hg, Option.bind_some]
      apply bind_total
      intro a member next
      let executePath := if shortable op then Formula.and a.path (.not (shortGuard op a.value)) else a.path
      obtain ⟨rhs, hright, hsr⟩ := ih (path := executePath) (start := next) hrhs hr.2 (hs a member) sr
      obtain ⟨executed, he, hse⟩ := bind_total (β := SymTerm) (input := rhs) (n := Γ.length)
        (action := fun b next => some (addCheck b.path (binaryGuard op a.value b.value)
          (single (.binary op a.value b.value) b.env b.path next)))
        (fun b hb next => ⟨_, rfl, shape_single (next := next) (hsr b hb)⟩)
      dsimp only [executePath] at hright
      simp only [hright, he, Option.bind_some]
      split
      · refine ⟨_, rfl, ?_⟩
        intro out hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hs a member
        · exact hse out hm
      · exact ⟨executed, rfl, hse⟩
    | @call f params result Γ args hf hargs =>
      have argsGenerate : ∀ arg ∈ args, ∀ env path next, env.length = Γ.length →
          ∃ generated, analyze fs preconditions height Γ arg env path next = some generated ∧
            Shape Γ.length generated := by
        intro arg member env path next he
        obtain ⟨ty, ht⟩ := args_member_type hargs member
        have smaller := argument_node_bound member
        have size : ceiling * bodyBound fs + nodes arg < height := by
          simp only [nodes] at heightBound
          omega
        exact ih ht (arguments_rank hr.2 member) he size
      obtain ⟨actuals, hactuals, actualShape⟩ := arguments_total (path := path) (next := start) argsGenerate hlen
      simp only [hactuals, Option.bind_some]
      apply bind_total
      intro out member next
      obtain ⟨fn, lookup, hparams, hresult⟩ := signatures_entry hf
      have shape := actualShape out member
      have arity : out.value.length = fn.params.length := shape.2.trans ((args_length hargs).trans (congrArg List.length hparams.symm))
      obtain ⟨⟨defined, truth⟩, hrequires⟩ := requires_total (hp f fn lookup) arity
      have small := rank_cost_decreases (args := args) hr.1 lookup
      have enough : rank f * bodyBound fs + nodes fn.body < height := by omega
      have entryLength : out.value.reverse.length = (LocalState.immutable fn.params.reverse).length := by
        simpa [LocalState.immutable] using arity
      obtain ⟨body, hbody, _⟩ := ih (path := out.path) (start := next)
        (wf f fn lookup) (ranked f fn lookup) entryLength enough
      refine ⟨addCheck out.path (.and defined truth) { body with outcomes := body.outcomes.map (fun result => { result with env := out.env }) }, ?_, ?_⟩
      · simp [lookup, arity, hrequires, hbody]
      · intro r member
        obtain ⟨prior, _, rfl⟩ := List.mem_map.mp member
        exact shape.1
    | @whileE invariants Γ condition body nonempty hinvariants hc hb =>
      have sc : ceiling * bodyBound fs + nodes condition < height := by simp only [nodes] at heightBound; omega
      have sb : ceiling * bodyBound fs + nodes body < height := by simp only [nodes] at heightBound; omega
      have notEmpty : invariants.isEmpty = false := by
        cases invariants with
        | nil => exact False.elim (nonempty rfl)
        | cons _ _ => rfl
      obtain ⟨⟨initial, truth⟩, hinit⟩ := assertions_total (path := path) hinvariants hlen
      obtain ⟨head, hhead, headLength⟩ := head_total (start := start) hlen
      obtain ⟨⟨headChecks, invariant⟩, hinv⟩ := assertions_total (path := path) hinvariants headLength
      let headPath := Formula.and path (.and head.domain invariant)
      obtain ⟨conditionResult, hcondition, conditionShape⟩ := ih (path := headPath) (start := head.next)
        hc hr.1 headLength sc
      dsimp only [headPath] at hcondition
      simp only [notEmpty, hinit, hhead, hinv, hcondition, Option.bind_some]
      obtain ⟨iterations, hiterations, iterationShape⟩ := bind_total (β := SymTerm) (input := conditionResult)
        (action := fun out next => do
          let bodyResult ← analyze fs preconditions height Γ body out.env (.and out.path (.holds out.value)) next
          let preservation : Analysis SymTerm ← bindAnalysis bodyResult fun final next => do
            let (checks, _) ← assertions final.env final.path invariants
            return ⟨[], checks, next⟩
          return addCheck out.path (.boolean out.value)
            ⟨[⟨.lit .unit, out.env, .and out.path (.holds (.unary .not out.value))⟩],
              preservation.checks, preservation.next⟩) (n := Γ.length) (by
          intro out member next
          obtain ⟨bodyResult, hbgen, bodyShape⟩ := ih (path := .and out.path (.holds out.value)) (start := next)
            hb hr.2 (conditionShape out member) sb
          obtain ⟨preservation, hpgen, _⟩ := bind_total (β := SymTerm) (input := bodyResult) (n := Γ.length)
            (action := fun final next => do
              let (checks, _) ← assertions final.env final.path invariants
              return ⟨[], checks, next⟩) (by
              intro final hmem next
              obtain ⟨⟨checks, inv⟩, hass⟩ := assertions_total (path := final.path) hinvariants (bodyShape final hmem)
              exact ⟨⟨[], checks, next⟩, by simp [hass], by intro _ h; cases h⟩)
          change bindAnalysis bodyResult (fun final next => (assertions final.env final.path invariants).bind
            (fun pair => some (⟨[], pair.1, next⟩ : Analysis SymTerm))) = some preservation at hpgen
          refine ⟨addCheck out.path (.boolean out.value)
            ⟨[⟨.lit .unit, out.env, .and out.path (.holds (.unary .not out.value))⟩],
              preservation.checks, preservation.next⟩, by simp [hbgen, hpgen], ?_⟩
          intro r hmem
          simp only [addCheck, List.mem_singleton] at hmem
          subst r
          exact conditionShape out member)
      dsimp only at hiterations
      simp only [bind, Option.pure_def] at hiterations
      exact ⟨{ iterations with checks := initial ++ iterations.checks }, by simp [hiterations], iterationShape⟩

end APL.LoopGeneration
