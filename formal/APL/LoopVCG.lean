import APL.LoopVCGSupport
import APL.LoopAnnotations

/-! A concrete invariant verification-condition generator for the local-state
model. Expansion height bounds syntax and call-body traversal, not loop
iterations. Guarded checks survive even when no normal outcome remains. -/

namespace APL.LoopVCG

open VCG

structure Outcome (α : Type) where
  value : α
  env : List SymTerm
  path : Formula

structure Analysis (α : Type) where
  outcomes : List (Outcome α)
  checks : List Check
  next : Nat

def single (value : α) (env : List SymTerm) (path : Formula) (next : Nat) : Analysis α :=
  ⟨[⟨value, env, path⟩], [], next⟩

def combine (a b : Analysis α) : Analysis α :=
  ⟨a.outcomes ++ b.outcomes, a.checks ++ b.checks, b.next⟩

def sequence (action : Outcome α → Nat → Option (Analysis β)) :
    List (Outcome α) → Nat → Option (Analysis β)
  | [], next => some ⟨[], [], next⟩
  | outcome :: rest, next => do
      let first ← action outcome next
      let tail ← sequence action rest first.next
      return combine first tail

def bindAnalysis (analysis : Analysis α) (action : Outcome α → Nat → Option (Analysis β)) :
    Option (Analysis β) := do
  let later ← sequence action analysis.outcomes analysis.next
  return { later with checks := analysis.checks ++ later.checks }

def addCheck (guard required : Formula) (analysis : Analysis α) : Analysis α :=
  { analysis with checks := ⟨guard, required⟩ :: analysis.checks }

theorem sequence_counter {α β : Type} {action : Outcome α → Nat → Option (Analysis β)}
    {outcomes : List (Outcome α)} {start : Nat} {generated : Analysis β}
    (ha : ∀ outcome start generated, action outcome start = some generated → start ≤ generated.next)
    (hg : sequence action outcomes start = some generated) : start ≤ generated.next := by
  induction outcomes generalizing start generated with
  | nil => cases hg; exact Nat.le_refl _
  | cons out rest ih =>
    simp only [sequence, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, hf, tail, ht, heq⟩ := hg
    cases heq
    exact Nat.le_trans (ha out start first hf) (ih (generated := tail) ht)

theorem bind_counter {α β : Type} {action : Outcome α → Nat → Option (Analysis β)}
    {input : Analysis α} {generated : Analysis β}
    (ha : ∀ outcome start generated, action outcome start = some generated → start ≤ generated.next)
    (hg : bindAnalysis input action = some generated) : input.next ≤ generated.next := by
  simp only [bindAnalysis, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨later, hl, heq⟩ := hg
  cases heq
  exact sequence_counter (generated := later) ha hl

def assertions (syms : List SymTerm) (path : Formula) :
    List LoopAnnotations.Assertion → Option (List Check × Formula)
  | [] => some ([], .truth true)
  | clause :: rest => do
      let term ← clause.instantiate syms
      let (checks, truth) ← assertions syms path rest
      let required := Formula.and (.defined term) (.holds term)
      return (⟨path, required⟩ :: checks, .and required truth)

def arguments
    (generate : LoopAnnotations.Term → List SymTerm → Formula → Nat → Option (Analysis SymTerm)) :
    List LoopAnnotations.Term → List SymTerm → Formula → Nat → Option (Analysis (List SymTerm))
  | [], env, path, next => some (single [] env path next)
  | arg :: rest, env, path, next => do
      let first ← generate arg env path next
      bindAnalysis first fun out next => do
        let remaining ← arguments generate rest out.env out.path next
        return { remaining with outcomes := remaining.outcomes.map fun r =>
          ⟨out.value :: r.value, r.env, r.path⟩ }

theorem arguments_counter
    {generate : LoopAnnotations.Term → List SymTerm → Formula → Nat → Option (Analysis SymTerm)}
    (ha : ∀ e env path start generated, generate e env path start = some generated → start ≤ generated.next)
    (hg : arguments generate args env path start = some generated) : start ≤ generated.next := by
  induction args generalizing env path start generated with
  | nil => cases hg; exact Nat.le_refl _
  | cons arg rest ih =>
    simp only [arguments, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨first, hf, hrest⟩ := hg
    apply Nat.le_trans (ha arg env path start first hf)
    apply bind_counter (hg := hrest)
    intro out next output haction
    simp only [Option.bind_eq_some_iff, Option.pure_def] at haction
    obtain ⟨remaining, hr, heq⟩ := haction
    cases heq
    exact ih (generated := remaining) hr

def analyze (fs : LoopAnnotations.Functions) (preconditions : Preconditions) :
    Nat → LocalState.Ctx → LoopAnnotations.Term → List SymTerm → Formula → Nat →
      Option (Analysis SymTerm)
  | 0, _, _, _, _, _ => none
  | height + 1, Γ, e, env, path, next => do
    let _ ← LocalState.infer (LoopAnnotations.signatures fs) Γ e.erase
    match e with
    | .lit v => return single (.lit (embed v)) env path next
    | .local i => return single (← env[i]?) env path next
    | .letE a b =>
      let ty ← LocalState.infer (LoopAnnotations.signatures fs) Γ a.erase
      let first ← analyze fs preconditions height Γ a env path next
      bindAnalysis first fun out next => do
        let body ← analyze fs preconditions height ((ty, false) :: Γ) b (out.value :: out.env) out.path next
        let results ← body.outcomes.mapM fun result => do
          let _ ← result.env.head?
          return { result with env := result.env.tail }
        return { body with outcomes := results }
    | .letMut a b =>
      let ty ← LocalState.infer (LoopAnnotations.signatures fs) Γ a.erase
      let first ← analyze fs preconditions height Γ a env path next
      bindAnalysis first fun out next => do
        let body ← analyze fs preconditions height ((ty, true) :: Γ) b (out.value :: out.env) out.path next
        let results ← body.outcomes.mapM fun result => do
          let _ ← result.env.head?
          return { result with env := result.env.tail }
        return { body with outcomes := results }
    | .assign i rhs =>
      let value ← analyze fs preconditions height Γ rhs env path next
      bindAnalysis value fun out next => do
        let updated ← StateVCG.updateSymbols out.env i out.value
        return single (.lit .unit) updated out.path next
    | .ifE condition yes no =>
      let test ← analyze fs preconditions height Γ condition env path next
      bindAnalysis test fun out next => do
        let a ← analyze fs preconditions height Γ yes out.env (.and out.path (.holds out.value)) next
        let b ← analyze fs preconditions height Γ no out.env
          (.and out.path (.holds (.unary .not out.value))) a.next
        return addCheck out.path (.boolean out.value) (combine a b)
    | .unary op arg =>
      let argument ← analyze fs preconditions height Γ arg env path next
      bindAnalysis argument fun out next =>
        some (addCheck out.path (unaryGuard op out.value)
          (single (.unary op out.value) out.env out.path next))
    | .binary op left right =>
      let lhs ← analyze fs preconditions height Γ left env path next
      bindAnalysis lhs fun a next => do
        let executePath := if shortable op then .and a.path (.not (shortGuard op a.value)) else a.path
        let rhs ← analyze fs preconditions height Γ right a.env executePath next
        let executed ← bindAnalysis rhs fun b next =>
          some (addCheck b.path (binaryGuard op a.value b.value)
            (single (.binary op a.value b.value) b.env b.path next))
        if shortable op then
          return { executed with outcomes :=
            ⟨a.value, a.env, .and a.path (shortGuard op a.value)⟩ :: executed.outcomes }
        else return executed
    | .call function args =>
      let actuals ← arguments (analyze fs preconditions height Γ) args env path next
      bindAnalysis actuals fun out next => do
        let fn ← fs[function]?
        if out.value.length = fn.params.length then
          let (defined, truth) ← requiresVC out.value (preconditions function)
          let body ← analyze fs preconditions height (LocalState.immutable fn.params.reverse)
            fn.body out.value.reverse out.path next
          return addCheck out.path (.and defined truth)
            { body with outcomes := body.outcomes.map fun result =>
                { result with env := out.env } }
        else none
    | .whileE clauses condition body =>
      if clauses.isEmpty then none else do
        let (initial, _) ← assertions env path clauses
        let head ← freshHead Γ env next
        let (_, invariant) ← assertions head.symbols path clauses
        let headPath := Formula.and path (.and head.domain invariant)
        let conditionResult ← analyze fs preconditions height Γ condition head.symbols headPath head.next
        let iterations ← bindAnalysis conditionResult fun out next => do
          let bodyResult ← analyze fs preconditions height Γ body out.env
            (.and out.path (.holds out.value)) next
          let preservation : Analysis SymTerm ← bindAnalysis bodyResult fun final next => do
            let (checks, _) ← assertions final.env final.path clauses
            return ⟨[], checks, next⟩
          return addCheck out.path (.boolean out.value)
            ⟨[⟨.lit .unit, out.env, .and out.path (.holds (.unary .not out.value))⟩],
              preservation.checks, preservation.next⟩
        return { iterations with checks := initial ++ iterations.checks }

theorem analyze_counter
    (hg : analyze fs preconditions height Γ e env path start = some generated) :
    start ≤ generated.next := by
  induction height generalizing Γ e env path start generated with
  | zero => simp [analyze] at hg
  | succ height ih =>
    simp only [analyze, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨ty, hinfer, hg⟩ := hg
    cases e with
    | lit v => cases hg; exact Nat.le_refl _
    | «local» i =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨symbol, hs, heq⟩ := hg
      cases heq
      exact Nat.le_refl _
    | letE a b | letMut a b =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨ty, ht, first, hf, hbody⟩ := hg
      apply Nat.le_trans (ih hf)
      apply bind_counter (hg := hbody)
      intro out next generated haction
      simp only [Option.bind_eq_some_iff, Option.pure_def] at haction
      obtain ⟨body, hb, results, _, heq⟩ := haction
      cases heq
      exact ih (generated := body) hb
    | assign i rhs =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨value, hv, haction⟩ := hg
      apply Nat.le_trans (ih hv)
      apply bind_counter (hg := haction)
      intro out next generated hupdate
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hupdate
      obtain ⟨updated, _, heq⟩ := hupdate
      cases heq
      exact Nat.le_refl _
    | ifE condition yes no =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨test, ht, hbranches⟩ := hg
      apply Nat.le_trans (ih ht)
      apply bind_counter (hg := hbranches)
      intro out next generated haction
      simp only [Option.bind_eq_some_iff, Option.pure_def] at haction
      obtain ⟨a, ha, b, hb, heq⟩ := haction
      cases heq
      exact Nat.le_trans (ih (generated := a) ha) (ih (generated := b) hb)
    | unary op arg =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨argument, ha, haction⟩ := hg
      apply Nat.le_trans (ih ha)
      apply bind_counter (hg := haction)
      intro out next generated heq
      cases heq
      exact Nat.le_refl _
    | binary op left right =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨lhs, hl, haction⟩ := hg
      apply Nat.le_trans (ih hl)
      apply bind_counter (hg := haction)
      intro a next generated hrhs
      simp only [Option.bind_eq_some_iff] at hrhs
      obtain ⟨rhs, hr, executed, he, hfinal⟩ := hrhs
      have hafter : rhs.next ≤ executed.next := by
        apply bind_counter (hg := he)
        intro b next output heq
        cases heq
        exact Nat.le_refl _
      split at hfinal <;> cases hfinal <;> exact Nat.le_trans (ih hr) hafter
    | call function args =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨actuals, ha, hcall⟩ := hg
      have hargs := arguments_counter
        (fun e env path start generated hg => ih (generated := generated) hg) ha
      apply Nat.le_trans hargs
      apply bind_counter (hg := hcall)
      intro out next generated haction
      simp only [Option.bind_eq_some_iff] at haction
      obtain ⟨fn, hf, hbody⟩ := haction
      split at hbody
      next arity =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at hbody
        obtain ⟨⟨defined, truth⟩, hp, body, hb, heq⟩ := hbody
        cases heq
        exact ih (generated := body) hb
      next => contradiction
    | whileE clauses condition body =>
      simp only [] at hg
      split at hg
      next => contradiction
      next =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
        obtain ⟨⟨initial, _⟩, hi, head, hh, ⟨_, invariant⟩, hinv,
          conditionResult, hc, iterations, hit, heq⟩ := hg
        cases heq
        have hhead : start ≤ head.next := by
          simp only [freshHead, bind, Option.bind_eq_some_iff, Option.pure_def] at hh
          obtain ⟨⟨symbols, final⟩, henv, domain, hdom, heq⟩ := hh
          cases heq
          have hshape := (fresh_shape henv).1
          change start ≤ final
          omega
        apply Nat.le_trans hhead
        apply Nat.le_trans (ih hc)
        apply bind_counter (generated := iterations) (hg := hit)
        intro out next generated haction
        simp only [Option.bind_eq_some_iff] at haction
        obtain ⟨bodyResult, hb, preservation, hp, heq⟩ := haction
        cases heq
        apply Nat.le_trans (ih hb)
        apply bind_counter (generated := preservation) (hg := hp)
        intro final next generated hass
        simp only [Option.bind_eq_some_iff] at hass
        obtain ⟨⟨checks, _⟩, hc, heq⟩ := hass
        cases heq
        exact Nat.le_refl _

-- Companion modules prove support bounds, actual-machine soundness, typed
-- contracts, and exact mathematical check partition. Global allocation-event
-- history, production correspondence, and resource policies remain outside them.

end APL.LoopVCG

namespace APL.LoopVCG

open VCG LoopAnnotations

def InvariantsHold (env : Env) (clauses : List Assertion) : Prop :=
  ∀ clause ∈ clauses, clause.eval (env.map VCG.embed) = some (.bool true)

theorem required_iff :
    (Formula.and (.defined term) (.holds term)).Holds model ↔
      term.eval model = some (.bool true) := by
  constructor
  · exact And.right
  · intro h
    exact ⟨⟨.bool true, h⟩, h⟩

theorem assertions_truth
    (hg : assertions syms path clauses = some (checks, truth))
    (he : EnvRep model syms env) : truth.Holds model ↔ InvariantsHold env clauses := by
  induction clauses generalizing checks truth with
  | nil =>
    cases hg
    simp [Formula.Holds, InvariantsHold]
  | cons clause rest ih =>
    simp only [assertions, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨term, ht, ⟨tail, formula⟩, htail, heq⟩ := hg
    cases heq
    change ((Formula.and (.defined term) (.holds term)).Holds model ∧ formula.Holds model) ↔ _
    rw [required_iff, Assertion.instantiate_sound ht he, ih htail]
    simp [InvariantsHold]

theorem assertions_group_exact
    (hg : assertions syms path clauses = some (checks, truth)) :
    (group checks).Holds model ↔ (path.Holds model → truth.Holds model) := by
  induction clauses generalizing checks truth with
  | nil =>
    cases hg
    simp [group, Formula.Holds]
  | cons clause rest ih =>
    simp only [assertions, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨term, ht, ⟨tail, formula⟩, htail, heq⟩ := hg
    cases heq
    change ((path.Holds model → (Formula.and (.defined term) (.holds term)).Holds model) ∧
      (group tail).Holds model) ↔
      (path.Holds model → (Formula.and (.defined term) (.holds term)).Holds model ∧ formula.Holds model)
    rw [ih htail]
    exact ⟨fun h hp => ⟨h.1 hp, h.2 hp⟩, fun h => ⟨fun hp => (h hp).1, fun hp => (h hp).2⟩⟩

theorem assertions_guards
    (hg : assertions syms path clauses = some (checks, truth)) :
    ∀ check ∈ checks, check.guard = path := by
  induction clauses generalizing checks truth with
  | nil => cases hg; simp
  | cons clause rest ih =>
    simp only [assertions, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨term, ht, ⟨tail, formula⟩, htail, heq⟩ := hg
    cases heq
    intro check member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · exact ih htail check member

theorem assertions_established
    (hg : assertions syms path clauses = some (checks, truth))
    (he : EnvRep model syms env) (hc : (group checks).Holds model)
    (hp : path.Holds model) : InvariantsHold env clauses :=
  (assertions_truth hg he).mp ((assertions_group_exact hg).mp hc hp)

theorem invariant_defined (h : InvariantsHold env clauses) (member : clause ∈ clauses) :
    ∃ value, clause.eval (env.map VCG.embed) = some value :=
  ⟨.bool true, h clause member⟩

end APL.LoopVCG
