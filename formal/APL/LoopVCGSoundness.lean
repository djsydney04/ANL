import APL.LocalStateContinuation
import APL.LoopVCGBounds

/-! Soundness of concrete invariant generation for actual LocalState.run and
Steps. Validity ranges over every model extension preserving earlier symbols.
The conclusions allow divergence and resource exhaustion; they do not establish
source-to-model, Rust flow, SMT, or solver correspondence. -/

namespace APL.LoopVCG

open VCG

def ValidFrom (bound : Nat) (model : Model) (checks : List Check) : Prop :=
  ∀ extended, AgreeBelow bound model extended → (group checks).Holds extended

def Covered (bound : Nat) (model : Model) (analysis : Analysis SymTerm)
    (value : Val) (env : Env) : Prop :=
  ∃ outcome ∈ analysis.outcomes, ∃ extended,
    AgreeBelow bound model extended ∧ outcome.path.Holds extended ∧
      Denotes extended outcome.value value ∧ EnvRep extended outcome.env env

theorem agree_refl : AgreeBelow bound model model := fun _ _ => rfl

theorem agree_trans (ha : AgreeBelow bound a b) (hb : AgreeBelow bound b c) :
    AgreeBelow bound a c := fun i hi => (ha i hi).trans (hb i hi)

theorem agree_restrict (h : AgreeBelow big a b) (hn : small ≤ big) :
    AgreeBelow small a b := fun i hi => h i (Nat.lt_of_lt_of_le hi hn)

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

theorem covered_subset (h : Covered bound model small value env)
    (hs : ∀ outcome ∈ small.outcomes, outcome ∈ big.outcomes) :
    Covered bound model big value env := by
  obtain ⟨out, hm, extended, ha, hp, hv, he⟩ := h
  exact ⟨out, hs out hm, extended, ha, hp, hv, he⟩

theorem covered_extend (h : Covered nextBound nextModel analysis value env)
    (ha : AgreeBelow bound model nextModel) (hn : bound ≤ nextBound) :
    Covered bound model analysis value env := by
  obtain ⟨out, hm, extended, hext, hp, hv, he⟩ := h
  exact ⟨out, hm, extended, agree_trans ha (agree_restrict hext hn), hp, hv, he⟩

private theorem lifted_value (h : VCG.Safe result (Program.liftResult actual 0)) :
    ∃ value, actual = .value value ∧ result value := by
  cases actual with
  | value value => exact ⟨value, rfl, h⟩
  | trap _ | invalid => exact False.elim h

-- Equality-filtering posts recover the concrete result denotation from the
-- already accepted primitive WP lemmas, without exposing old private lemmas.
theorem unary_guard_value (ha : Denotes model symbol value)
    (hg : (unaryGuard op symbol).Holds model) :
    ∃ actual, unary op value = .value actual ∧ Denotes model (.unary op symbol) actual := by
  classical
  let post : Post := fun s => if s = .unary op symbol then some (.truth true) else none
  have generated : unaryWP op symbol post = some (.and (unaryGuard op symbol) (.truth true)) := by
    simp [unaryWP, post]
  obtain ⟨actual, heval, s, formula, hpost, _, hdenotes⟩ :=
    lifted_value (unary_wp_sound (fuel := 0) generated ⟨hg, rfl⟩ ha)
  have eq : s = .unary op symbol := by
    by_cases hs : s = .unary op symbol
    · exact hs
    · simp [post, hs] at hpost
  exact ⟨actual, heval, eq ▸ hdenotes⟩

theorem binary_guard_value (ha : Denotes model left a) (hb : Denotes model right b)
    (hs : shortCircuit op a = false) (hg : (binaryGuard op left right).Holds model) :
    ∃ actual, binary op a b = .value actual ∧ Denotes model (.binary op left right) actual := by
  classical
  let post : Post := fun s => if s = .binary op left right then some (.truth true) else none
  have generated : binaryWP op left right post =
      some (.and (binaryGuard op left right) (.truth true)) := by simp [binaryWP, post]
  obtain ⟨actual, heval, s, formula, hpost, _, hdenotes⟩ :=
    lifted_value (binary_wp_sound (fuel := 0) generated ⟨hg, rfl⟩ ha hb hs)
  have eq : s = .binary op left right := by
    by_cases heq : s = .binary op left right
    · exact heq
    · simp [post, heq] at hpost
  exact ⟨actual, heval, eq ▸ hdenotes⟩

theorem sequence_locate {α β : Type} {action : Outcome α → Nat → Option (Analysis β)}
    {outcomes : List (Outcome α)} {start : Nat} {generated : Analysis β} {out : Outcome α}
    (ha : ∀ out next result, action out next = some result → next ≤ result.next)
    (hg : sequence action outcomes start = some generated) (hm : out ∈ outcomes) :
    ∃ next result, start ≤ next ∧ action out next = some result ∧
      (∀ outcome ∈ result.outcomes, outcome ∈ generated.outcomes) ∧
      (∀ check ∈ result.checks, check ∈ generated.checks) := by
  induction outcomes generalizing start generated with
  | nil => simp at hm
  | cons first rest ih =>
    simp only [sequence, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨firstResult, hf, tail, ht, heq⟩ := hg
    cases heq
    rcases List.mem_cons.mp hm with rfl | hrest
    · refine ⟨start, firstResult, Nat.le_refl _, hf, ?_, ?_⟩
      · intro outcome ho
        exact List.mem_append_left _ ho
      · intro check hc
        exact List.mem_append_left _ hc
    · obtain ⟨next, result, hnext, hresult, ho, hc⟩ := ih ht hrest
      refine ⟨next, result, Nat.le_trans (ha first start firstResult hf) hnext, hresult, ?_, ?_⟩
      · intro outcome hm
        exact List.mem_append_right _ (ho outcome hm)
      · intro check hm
        exact List.mem_append_right _ (hc check hm)

theorem bind_locate {α β : Type} {action : Outcome α → Nat → Option (Analysis β)}
    {input : Analysis α} {generated : Analysis β} {out : Outcome α}
    (ha : ∀ out next result, action out next = some result → next ≤ result.next)
    (hg : bindAnalysis input action = some generated) (hm : out ∈ input.outcomes) :
    ∃ next result, input.next ≤ next ∧ action out next = some result ∧
      (∀ outcome ∈ result.outcomes, outcome ∈ generated.outcomes) ∧
      (∀ check ∈ result.checks, check ∈ generated.checks) := by
  simp only [bindAnalysis, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨later, hl, heq⟩ := hg
  cases heq
  obtain ⟨next, result, hnext, hresult, ho, hc⟩ := sequence_locate ha hl hm
  refine ⟨next, result, hnext, hresult, ho, ?_⟩
  intro check hm
  exact List.mem_append_right _ (hc check hm)

theorem bind_input_checks {α β : Type} {action : Outcome α → Nat → Option (Analysis β)}
    {input : Analysis α} {generated : Analysis β}
    (hg : bindAnalysis input action = some generated) :
    ∀ check ∈ input.checks, check ∈ generated.checks := by
  simp only [bindAnalysis, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨later, _, heq⟩ := hg
  cases heq
  intro check hm
  exact List.mem_append_left _ hm

theorem bind_context {action : Outcome SymTerm → Nat → Option (Analysis SymTerm)}
    {input generated : Analysis SymTerm}
    (ha : ∀ out next result, action out next = some result → next ≤ result.next)
    (hg : bindAnalysis input action = some generated)
    (hn : bound ≤ input.next)
    (hb : ∀ out ∈ input.outcomes, Below input.next out.value ∧
      SymbolsBelow input.next out.env ∧ FormulaBelow input.next out.path)
    (hv : ValidFrom bound model generated.checks)
    (hc : Covered bound model input value env) :
    ∃ out next result extended,
      out ∈ input.outcomes ∧ input.next ≤ next ∧ action out next = some result ∧
      AgreeBelow bound model extended ∧ out.path.Holds extended ∧
      Denotes extended out.value value ∧ EnvRep extended out.env env ∧
      Below next out.value ∧ SymbolsBelow next out.env ∧ FormulaBelow next out.path ∧
      ValidFrom next extended result.checks ∧
      (∀ value final, Covered next extended result value final →
        Covered bound model generated value final) := by
  obtain ⟨out, hm, extended, hext, hp, hvalue, henv⟩ := hc
  obtain ⟨next, result, hnext, hresult, houts, hchecks⟩ := bind_locate ha hg hm
  have hbound := hb out hm
  have valid := valid_extend (valid_subset hv hchecks) hext (Nat.le_trans hn hnext)
  refine ⟨out, next, result, extended, hm, hnext, hresult, hext, hp, hvalue, henv,
    below_mono hbound.1 hnext, symbols_below_mono hbound.2.1 hnext,
    formula_bound_mono hbound.2.2 hnext, valid, ?_⟩
  intro value final covered
  exact covered_subset (covered_extend covered hext (Nat.le_trans hn hnext)) houts

def SoundAt (fs : LocalState.Functions) (e : LocalState.Term) (Γ : LocalState.Ctx)
    (syms : List SymTerm) (path : Formula) (start : Nat) (analysis : Analysis SymTerm) : Prop :=
  ∀ model env, EnvRep model syms env → LocalState.EnvTyped env Γ → path.Holds model →
    ValidFrom start model analysis.checks →
    LocalState.LoopVerification.EvalSpec fs e env (Covered start model analysis)

theorem single_covered (hvalue : Denotes model symbol value) (henv : EnvRep model syms env)
    (hp : path.Holds model) : Covered next model (single symbol syms path next) value env :=
  ⟨⟨symbol, syms, path⟩, by simp [single], model, agree_refl, hp, hvalue, henv⟩

theorem literal_sound : SoundAt fs (.lit value) Γ syms path start
    (single (.lit (embed value)) syms path start) := by
  intro model env henv _ hp _
  apply LocalState.LoopVerification.spec_mono LocalState.LoopVerification.literal_rule
  intro actual final hout
  obtain ⟨rfl, rfl⟩ := hout
  exact single_covered rfl henv hp

theorem local_sound (lookup : syms[index]? = some symbol) :
    SoundAt fs (.local index) Γ syms path start (single symbol syms path start) := by
  intro model env henv _ hp _
  obtain ⟨value, hlookup, hvalue⟩ := EnvRep.lookup henv lookup
  apply LocalState.LoopVerification.spec_mono (LocalState.LoopVerification.local_rule hlookup)
  intro actual final hout
  obtain ⟨rfl, rfl⟩ := hout
  exact single_covered hvalue henv hp

-- A constructor induction step: its child SoundAt premise must be proved by the
-- smaller-height generator induction, not assumed as program verification.
theorem unary_analysis_sound
    (hc : SoundAt fs arg Γ syms path start first)
    (hn : start ≤ first.next)
    (hb : ∀ out ∈ first.outcomes, Below first.next out.value ∧
      SymbolsBelow first.next out.env ∧ FormulaBelow first.next out.path)
    (hg : bindAnalysis first (fun out next =>
      some (addCheck out.path (unaryGuard op out.value)
        (single (.unary op out.value) out.env out.path next))) = some generated) :
    SoundAt fs (.unary op arg) Γ syms path start generated := by
  intro model env henv htyped hp hvalid
  apply LocalState.LoopVerification.unary_rule
  apply LocalState.LoopVerification.spec_mono
    (hc model env henv htyped hp (valid_subset hvalid (bind_input_checks hg)))
  intro value current covered
  have hcounter : ∀ (out : Outcome SymTerm) (next : Nat) (result : Analysis SymTerm),
      some (addCheck out.path (unaryGuard op out.value)
        (single (.unary op out.value) out.env out.path next)) = some result → next ≤ result.next := by
    intro out next result heq
    cases heq
    exact Nat.le_refl _
  obtain ⟨out, next, result, extended, _, _, hresult, _, hpath, hvalue, hcurrent,
    _, _, _, actionValid, transfer⟩ := bind_context hcounter hg hn hb hvalid covered
  cases hresult
  have guard := valid_member actionValid
    (check := ⟨out.path, unaryGuard op out.value⟩) (by simp [addCheck]) agree_refl hpath
  obtain ⟨actual, heval, hdenotes⟩ := unary_guard_value hvalue guard
  refine ⟨actual, heval, transfer actual current ?_⟩
  exact single_covered hdenotes hcurrent hpath

theorem assignment_analysis_sound
    (hc : SoundAt fs rhs Γ syms path start first)
    (hn : start ≤ first.next)
    (hb : ∀ out ∈ first.outcomes, Below first.next out.value ∧
      SymbolsBelow first.next out.env ∧ FormulaBelow first.next out.path)
    (hg : bindAnalysis first (fun out next => do
      let updated ← StateVCG.updateSymbols out.env index out.value
      return single (.lit .unit) updated out.path next) = some generated) :
    SoundAt fs (.assign index rhs) Γ syms path start generated := by
  intro model env henv htyped hp hvalid
  apply LocalState.LoopVerification.assignment_rule
  apply LocalState.LoopVerification.spec_mono
    (hc model env henv htyped hp (valid_subset hvalid (bind_input_checks hg)))
  intro value current covered
  have hcounter : ∀ (out : Outcome SymTerm) (next : Nat) (result : Analysis SymTerm),
      (StateVCG.updateSymbols out.env index out.value).bind (fun updated =>
        some (single (.lit .unit) updated out.path next)) = some result → next ≤ result.next := by
    intro out next result hupdate
    simp only [Option.bind_eq_some_iff] at hupdate
    obtain ⟨updated, _, heq⟩ := hupdate
    cases heq
    exact Nat.le_refl _
  obtain ⟨out, next, result, extended, _, _, hresult, _, hpath, hvalue, hcurrent,
    _, _, _, _, transfer⟩ := bind_context hcounter hg hn hb hvalid covered
  simp only [Option.bind_eq_some_iff] at hresult
  obtain ⟨updated, hupdate, heq⟩ := hresult
  cases heq
  obtain ⟨final, hfinal, hrep⟩ := StateVCG.update_rep hcurrent hvalue hupdate
  exact ⟨final, hfinal, transfer .unit final (single_covered rfl hrep hpath)⟩

end APL.LoopVCG

namespace APL.LoopVCG

open VCG

def popOutcome (out : Outcome SymTerm) : Option (Outcome SymTerm) := do
  let _ ← out.env.head?
  return { out with env := out.env.tail }

theorem mapM_member {f : α → Option β} {inputs : List α} {outputs : List β}
    (hg : inputs.mapM f = some outputs)
    (hm : input ∈ inputs) : ∃ output, f input = some output ∧ output ∈ outputs := by
  induction inputs generalizing outputs with
  | nil => simp at hm
  | cons first rest ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨firstOut, hf, restOut, ht, heq⟩ := hg
    cases heq
    rcases List.mem_cons.mp hm with rfl | hr
    · exact ⟨firstOut, hf, by simp⟩
    · obtain ⟨out, ho, hm⟩ := ih ht hr
      exact ⟨out, ho, List.mem_cons_of_mem _ hm⟩

theorem scope_covered (hg : body.outcomes.mapM popOutcome = some results)
    (hc : Covered next model body value current) :
    ∃ cell rest, current = cell :: rest ∧
      Covered next model { body with outcomes := results } value rest := by
  obtain ⟨out, hm, extended, hext, hp, hvalue, hcurrent⟩ := hc
  obtain ⟨mapped, hpop, hmember⟩ := mapM_member hg hm
  obtain ⟨symbol, syms, path⟩ := out
  cases syms with
  | nil => simp [popOutcome] at hpop
  | cons s syms =>
    simp only [popOutcome, List.head?_cons, bind, Option.bind_some, Option.pure_def,
      List.tail_cons, Option.some.injEq] at hpop
    cases hpop
    cases hcurrent with
    | cons _ htail =>
      exact ⟨_, _, rfl, ⟨_, hmember, extended, hext, hp, hvalue, htail⟩⟩

theorem binding_analysis_sound {permission : Bool}
    {generate : List SymTerm → Formula → Nat → Option (Analysis SymTerm)}
    (wf : LocalState.WellTyped fs)
    (ht : LocalState.HasType (LocalState.signatures fs) Γ a ty)
    (hc : SoundAt fs a Γ syms path start first)
    (hn : start ≤ first.next)
    (hb : ∀ out ∈ first.outcomes, Below first.next out.value ∧
      SymbolsBelow first.next out.env ∧ FormulaBelow first.next out.path)
    (gc : ∀ syms path next body, generate syms path next = some body → next ≤ body.next)
    (gs : ∀ syms path next body, generate syms path next = some body →
      SymbolsBelow next syms → FormulaBelow next path →
      SoundAt fs b ((ty, permission) :: Γ) syms path next body)
    (hg : bindAnalysis first (fun out next => do
      let body ← generate (out.value :: out.env) out.path next
      let results ← body.outcomes.mapM popOutcome
      return { body with outcomes := results }) = some generated) :
    SoundAt fs (if permission then .letMut a b else .letE a b) Γ syms path start generated := by
  intro model env henv htyped hp hvalid
  apply LocalState.LoopVerification.binding_rule
    (LocalState.LoopVerification.spec_frame
      (hc model env henv htyped hp (valid_subset hvalid (bind_input_checks hg))) wf ht htyped)
  intro value current hout
  obtain ⟨covered, _, currentTyped, valueTyped⟩ := hout
  have hcounter : ∀ (out : Outcome SymTerm) (next : Nat) (result : Analysis SymTerm),
      (do let body ← generate (out.value :: out.env) out.path next
          let results ← body.outcomes.mapM popOutcome
          pure { body with outcomes := results }) = some result → next ≤ result.next := by
    intro out next result haction
    simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at haction
    obtain ⟨body, hbody, results, _, heq⟩ := haction
    cases heq
    exact gc _ _ _ body hbody
  obtain ⟨out, next, result, extended, _, _, hresult, _, hpath, hvalue, hcurrent,
    valueBound, envBound, pathBound, actionValid, transfer⟩ := bind_context hcounter hg hn hb hvalid covered
  simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at hresult
  obtain ⟨body, hbody, results, hscope, heq⟩ := hresult
  cases heq
  have bodyEnv : LocalState.EnvTyped (value :: current) ((ty, permission) :: Γ) := by
    simpa only [valueTyped] using (LocalState.env_cons (permission := permission) currentTyped (v := value))
  apply LocalState.LoopVerification.spec_mono
    (gs _ _ _ _ hbody ⟨valueBound, envBound⟩ pathBound
      extended (value :: current) (.cons hvalue hcurrent) bodyEnv hpath actionValid)
  intro actual final hcovered
  obtain ⟨cell, rest, heq, hfinal⟩ := scope_covered hscope hcovered
  exact ⟨cell, rest, heq, transfer actual rest hfinal⟩

end APL.LoopVCG

namespace APL.LoopVCG

open VCG
open LocalState.LoopVerification

theorem boolean_denotes (hv : Denotes model symbol value)
    (hb : (Formula.boolean symbol).Holds model) : ∃ test, value = .bool test := by
  obtain ⟨test, ht⟩ := hb
  unfold Denotes at hv
  rw [hv] at ht
  cases value with
  | int _ | unit => cases ht
  | bool value => exact ⟨value, rfl⟩

theorem true_denotes (hv : Denotes model symbol (.bool true)) :
    (Formula.holds symbol).Holds model := hv

theorem false_denotes (hv : Denotes model symbol (.bool false)) :
    (Formula.holds (.unary .not symbol)).Holds model := by
  change symbol.eval model = some (.bool false) at hv
  simp only [Formula.Holds, SymTerm.eval, hv, bind, Option.bind, mUnary]
  rfl

def conditionalAction (fs : LoopAnnotations.Functions) (preconditions : Preconditions)
    (height : Nat) (Γ : LocalState.Ctx) (yes no : LoopAnnotations.Term)
    (out : Outcome SymTerm) (next : Nat) : Option (Analysis SymTerm) := do
  let a ← analyze fs preconditions height Γ yes out.env (.and out.path (.holds out.value)) next
  let b ← analyze fs preconditions height Γ no out.env
    (.and out.path (.holds (.unary .not out.value))) a.next
  return addCheck out.path (.boolean out.value) (combine a b)

theorem conditional_counter
    (hg : conditionalAction fs preconditions height Γ yes no out next = some generated) :
    next ≤ generated.next := by
  simp only [conditionalAction, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨a, ha, b, hb, heq⟩ := hg
  cases heq
  exact Nat.le_trans (analyze_counter ha) (analyze_counter (generated := b) hb)

theorem conditional_analysis_sound {condition : LoopAnnotations.Term}
    (wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions fs))
    (ht : LocalState.HasType (LocalState.signatures (LoopAnnotations.eraseFunctions fs)) Γ condition.erase conditionTy)
    (hc : SoundAt (LoopAnnotations.eraseFunctions fs) condition.erase Γ syms path start first)
    (hn : start ≤ first.next)
    (hb : ∀ out ∈ first.outcomes, Below first.next out.value ∧
      SymbolsBelow first.next out.env ∧ FormulaBelow first.next out.path)
    (ih : ∀ {e syms path start generated},
      analyze fs preconditions height Γ e syms path start = some generated →
      SymbolsBelow start syms → FormulaBelow start path →
      SoundAt (LoopAnnotations.eraseFunctions fs) e.erase Γ syms path start generated)
    (hg : bindAnalysis first (conditionalAction fs preconditions height Γ yes no) = some generated) :
    SoundAt (LoopAnnotations.eraseFunctions fs) (.ifE condition.erase yes.erase no.erase)
      Γ syms path start generated := by
  intro model env henv htyped hp hvalid
  let Branch := fun test current => Covered start model first (.bool test) current ∧ LocalState.EnvTyped current Γ
  apply conditional_rule (branch := Branch)
  · apply spec_mono (spec_frame
      (hc model env henv htyped hp (valid_subset hvalid (bind_input_checks hg))) wf ht htyped)
    intro value current hnormal
    obtain ⟨covered, _, currentTyped, _⟩ := hnormal
    obtain ⟨out, next, result, extended, _, _, hresult, _, hpath, hvalue, _, _, _, _, valid, _⟩ :=
      bind_context (fun _ _ _ h => conditional_counter h) hg hn hb hvalid covered
    simp only [conditionalAction, bind, Option.bind_eq_some_iff, Option.pure_def] at hresult
    obtain ⟨a, ha, b, hbb, heq⟩ := hresult
    cases heq
    have boolCheck := valid_member valid (check := ⟨out.path, .boolean out.value⟩)
      (by simp [addCheck]) agree_refl hpath
    obtain ⟨test, rfl⟩ := boolean_denotes hvalue boolCheck
    exact ⟨test, rfl, covered, currentTyped⟩
  · intro test current hbranch
    obtain ⟨covered, currentTyped⟩ := hbranch
    obtain ⟨out, next, result, extended, _, _, hresult, _, hpath, hvalue, hcurrent,
      valueBound, envBound, pathBound, valid, transfer⟩ :=
      bind_context (fun _ _ _ h => conditional_counter h) hg hn hb hvalid covered
    simp only [conditionalAction, bind, Option.bind_eq_some_iff, Option.pure_def] at hresult
    obtain ⟨a, ha, b, hbb, heq⟩ := hresult
    cases heq
    cases test with
    | true =>
      have branchValid : ValidFrom next extended a.checks := valid_subset valid (by
        intro check member
        exact List.mem_cons_of_mem _ (List.mem_append_left _ member))
      apply spec_mono ((ih ha envBound ⟨pathBound, valueBound⟩)
        extended current hcurrent currentTyped ⟨hpath, true_denotes hvalue⟩ branchValid)
      intro value final covered
      apply transfer value final
      exact covered_subset covered (by intro out member; exact List.mem_append_left _ member)
    | false =>
      have afterYes := analyze_counter ha
      have branchValid : ValidFrom a.next extended b.checks :=
        valid_extend (valid_subset valid (by
          intro check member
          exact List.mem_cons_of_mem _ (List.mem_append_right _ member))) agree_refl afterYes
      apply spec_mono ((ih hbb (symbols_below_mono envBound afterYes)
          (formula_bound_mono ⟨pathBound, valueBound⟩ afterYes))
        extended current hcurrent currentTyped ⟨hpath, false_denotes hvalue⟩ branchValid)
      intro value final covered
      apply transfer value final
      exact covered_subset (covered_extend covered agree_refl afterYes)
        (by intro out member; exact List.mem_append_right _ member)

def binaryFinish (op : BOp) (left : SymTerm) (out : Outcome SymTerm) (next : Nat) :
    Option (Analysis SymTerm) :=
  some (addCheck out.path (binaryGuard op left out.value)
    (single (.binary op left out.value) out.env out.path next))

theorem binary_finish_counter
    (hg : binaryFinish op left out next = some generated) : next ≤ generated.next := by
  cases hg
  exact Nat.le_refl _

def binaryAction (fs : LoopAnnotations.Functions) (preconditions : Preconditions)
    (height : Nat) (Γ : LocalState.Ctx) (op : BOp) (right : LoopAnnotations.Term)
    (out : Outcome SymTerm) (next : Nat) : Option (Analysis SymTerm) := do
  let executePath := if shortable op then .and out.path (.not (shortGuard op out.value)) else out.path
  let rhs ← analyze fs preconditions height Γ right out.env executePath next
  let executed ← bindAnalysis rhs (binaryFinish op out.value)
  if shortable op then
    return { executed with outcomes :=
      ⟨out.value, out.env, .and out.path (shortGuard op out.value)⟩ :: executed.outcomes }
  else return executed

theorem binary_counter
    (hg : binaryAction fs preconditions height Γ op right out next = some generated) :
    next ≤ generated.next := by
  simp only [binaryAction, bind, Option.bind_eq_some_iff] at hg
  obtain ⟨rhs, hr, executed, he, hfinal⟩ := hg
  have hn := bind_counter (fun _ _ _ h => binary_finish_counter h) he
  split at hfinal <;> cases hfinal <;> exact Nat.le_trans (analyze_counter hr) hn

private theorem short_guard_bound (h : Below n value) : FormulaBelow n (shortGuard op value) := by
  cases op <;> simp_all [shortGuard, FormulaBelow, Below]

private theorem execute_path_bound (hp : FormulaBelow n path) (hv : Below n value) :
    FormulaBelow n (if shortable op then .and path (.not (shortGuard op value)) else path) := by
  split
  · exact ⟨hp, short_guard_bound hv⟩
  · exact hp

private theorem execute_path_holds (hp : path.Holds model) (hv : Denotes model symbol value)
    (hs : shortCircuit op value = false) :
    (if shortable op then Formula.and path (.not (shortGuard op symbol)) else path).Holds model := by
  split
  · refine ⟨hp, ?_⟩
    intro hshort
    have ht := (short_guard hv).mp hshort
    rw [hs] at ht
    contradiction
  · exact hp

theorem binary_analysis_sound {left : LoopAnnotations.Term}
    (wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions fs))
    (ht : LocalState.HasType (LocalState.signatures (LoopAnnotations.eraseFunctions fs)) Γ left.erase leftTy)
    (hc : SoundAt (LoopAnnotations.eraseFunctions fs) left.erase Γ syms path start first)
    (hn : start ≤ first.next)
    (hb : ∀ out ∈ first.outcomes, Below first.next out.value ∧
      SymbolsBelow first.next out.env ∧ FormulaBelow first.next out.path)
    (ih : ∀ {e syms path start generated},
      analyze fs preconditions height Γ e syms path start = some generated →
      SymbolsBelow start syms → FormulaBelow start path →
      SoundAt (LoopAnnotations.eraseFunctions fs) e.erase Γ syms path start generated)
    (support : ∀ {syms path start generated},
      analyze fs preconditions height Γ right syms path start = some generated →
      SymbolsBelow start syms → FormulaBelow start path →
      ∀ out ∈ generated.outcomes, Below generated.next out.value ∧
        SymbolsBelow generated.next out.env ∧ FormulaBelow generated.next out.path)
    (hg : bindAnalysis first (binaryAction fs preconditions height Γ op right) = some generated) :
    SoundAt (LoopAnnotations.eraseFunctions fs) (.binary op left.erase right.erase)
      Γ syms path start generated := by
  intro model env henv htyped hp hvalid
  let Middle := fun value current => Covered start model first value current ∧ LocalState.EnvTyped current Γ
  apply binary_rule (middle := Middle)
  · apply spec_mono (spec_frame
      (hc model env henv htyped hp (valid_subset hvalid (bind_input_checks hg))) wf ht htyped)
    intro value current hnormal
    exact ⟨hnormal.1, hnormal.2.2.1⟩
  · intro value current hmiddle hshort
    obtain ⟨covered, _⟩ := hmiddle
    obtain ⟨out, next, result, extended, _, _, hresult, _, hpath, hvalue, hcurrent,
      _, _, _, _, transfer⟩ :=
      bind_context (fun _ _ _ h => binary_counter h) hg hn hb hvalid covered
    have shortableTrue : shortable op = true := by
      cases hs : shortable op with
      | true => rfl
      | false => have impossible := not_shortable (v := value) hs; rw [hshort] at impossible; contradiction
    simp only [binaryAction, bind, Option.bind_eq_some_iff] at hresult
    obtain ⟨rhs, hr, executed, he, hfinal⟩ := hresult
    simp only [shortableTrue, ↓reduceIte, Option.pure_def, Option.some.injEq] at hfinal
    cases hfinal
    apply transfer value current
    exact ⟨⟨out.value, out.env, .and out.path (shortGuard op out.value)⟩, by simp,
      extended, agree_refl, ⟨hpath, (short_guard hvalue).mpr hshort⟩, hvalue, hcurrent⟩
  · intro value current hmiddle hshort
    obtain ⟨covered, currentTyped⟩ := hmiddle
    obtain ⟨out, next, result, extended, _, _, hresult, _, hpath, hvalue, hcurrent,
      valueBound, envBound, pathBound, actionValid, transfer⟩ :=
      bind_context (fun _ _ _ h => binary_counter h) hg hn hb hvalid covered
    simp only [binaryAction, bind, Option.bind_eq_some_iff] at hresult
    obtain ⟨rhs, hr, executed, he, hfinal⟩ := hresult
    have checksEqual : result.checks = executed.checks := by
      split at hfinal <;> cases hfinal <;> rfl
    have outcomeSubset : ∀ out ∈ executed.outcomes, out ∈ result.outcomes := by
      intro out member
      split at hfinal <;> cases hfinal
      · exact List.mem_cons_of_mem _ member
      · exact member
    have executedValid : ValidFrom next extended executed.checks := by
      rw [← checksEqual]
      exact actionValid
    have executeBound := execute_path_bound (op := op) pathBound valueBound
    have rhsValid := valid_subset executedValid (bind_input_checks he)
    apply spec_mono ((ih hr envBound executeBound) extended current hcurrent currentTyped
      (execute_path_holds hpath hvalue hshort) rhsValid)
    intro other final rightCovered
    obtain ⟨rightOut, finish, primitive, finalModel, _, _, primitiveGen, modelExt, rightPath,
      rightValue, finalEnv, _, _, _, primitiveValid, rightTransfer⟩ :=
      bind_context (fun _ _ _ h => binary_finish_counter h) he (analyze_counter hr)
        (support hr envBound executeBound) executedValid rightCovered
    cases primitiveGen
    have leftValue := denotes_agree valueBound modelExt hvalue
    have primitiveGuard := valid_member primitiveValid
      (check := ⟨rightOut.path, binaryGuard op out.value rightOut.value⟩)
      (by simp [addCheck]) agree_refl rightPath
    obtain ⟨actual, actualResult, actualValue⟩ := binary_guard_value leftValue rightValue hshort primitiveGuard
    refine ⟨actual, actualResult, transfer actual final ?_⟩
    apply covered_subset (hs := outcomeSubset)
    apply rightTransfer actual final
    exact single_covered actualValue finalEnv rightPath

end APL.LoopVCG

namespace APL.LoopVCG

open VCG
open LocalState.LoopVerification

def preserveAction (clauses : List LoopAnnotations.Assertion) (out : Outcome SymTerm)
    (next : Nat) : Option (Analysis SymTerm) := do
  let (checks, _) ← assertions out.env out.path clauses
  return ⟨[], checks, next⟩

def falseOutcome (out : Outcome SymTerm) : Outcome SymTerm :=
  ⟨.lit .unit, out.env, .and out.path (.holds (.unary .not out.value))⟩

def loopAction (clauses : List LoopAnnotations.Assertion)
    (generate : List SymTerm → Formula → Nat → Option (Analysis SymTerm))
    (out : Outcome SymTerm) (next : Nat) : Option (Analysis SymTerm) := do
  let body ← generate out.env (.and out.path (.holds out.value)) next
  let preservation ← bindAnalysis body (preserveAction clauses)
  return addCheck out.path (.boolean out.value)
    ⟨[falseOutcome out], preservation.checks, preservation.next⟩

theorem preserve_counter (hg : preserveAction clauses out next = some result) : next ≤ result.next := by
  simp only [preserveAction, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨⟨checks, _⟩, _, heq⟩ := hg
  cases heq
  exact Nat.le_refl _

theorem action_counter
    (gc : ∀ syms path next body, generate syms path next = some body → next ≤ body.next)
    (hg : loopAction clauses generate out next = some result) : next ≤ result.next := by
  simp only [loopAction, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨body, hb, preservation, hp, heq⟩ := hg
  cases heq
  exact Nat.le_trans (gc _ _ _ body hb)
    (bind_counter (generated := preservation) (fun _ _ _ h => preserve_counter h) hp)

theorem action_false (hg : loopAction clauses generate out next = some result) :
    falseOutcome out ∈ result.outcomes := by
  simp only [loopAction, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨body, _, preservation, _, heq⟩ := hg
  cases heq
  simp [addCheck]

theorem false_guard (h : Denotes model symbol (.bool false)) :
    (Formula.holds (.unary .not symbol)).Holds model := by
  unfold Denotes at h
  simp [Formula.Holds, SymTerm.eval, h, embed, mUnary]

theorem loop_analysis_sound
    {generate : List SymTerm → Formula → Nat → Option (Analysis SymTerm)}
    (wf : LocalState.WellTyped fs)
    (htc : LocalState.HasType (LocalState.signatures fs) Γ condition .bool)
    (htb : LocalState.HasType (LocalState.signatures fs) Γ body .unit)
    (hs : SymbolsBelow start syms) (hpath : FormulaBelow start path)
    (hi : assertions syms path clauses = some (initial, initialTruth))
    (hh : freshHead Γ syms start = some head)
    (hinv : assertions head.symbols path clauses = some (headChecks, invariant))
    (cs : SoundAt fs condition Γ head.symbols (.and path (.and head.domain invariant))
      head.next conditionResult)
    (cn : head.next ≤ conditionResult.next)
    (cb : ∀ out ∈ conditionResult.outcomes, Below conditionResult.next out.value ∧
      SymbolsBelow conditionResult.next out.env ∧ FormulaBelow conditionResult.next out.path)
    (gc : ∀ syms path next generated, generate syms path next = some generated → next ≤ generated.next)
    (gs : ∀ syms path next generated, generate syms path next = some generated →
      SymbolsBelow next syms → FormulaBelow next path → SoundAt fs body Γ syms path next generated)
    (gb : ∀ syms path next generated, generate syms path next = some generated →
      SymbolsBelow next syms → FormulaBelow next path → ∀ out ∈ generated.outcomes,
        Below generated.next out.value ∧ SymbolsBelow generated.next out.env ∧
          FormulaBelow generated.next out.path)
    (hg : bindAnalysis conditionResult (loopAction clauses generate) = some iterations) :
    SoundAt fs (.whileE condition body) Γ syms path start
      { iterations with checks := initial ++ iterations.checks } := by
  intro model entry hentry entryTyped entryPath accepted
  have hn := (fresh_head_bounded hh hs).1
  have htotal := Nat.le_trans hn cn
  have iterationValid : ValidFrom start model iterations.checks :=
    valid_subset accepted (fun _ hm => List.mem_append_right _ hm)
  have conditionValid : ValidFrom start model conditionResult.checks :=
    valid_subset iterationValid (bind_input_checks hg)
  let I : Env → Prop := fun current => LocalState.Frozen Γ entry current ∧
    LocalState.EnvTyped current Γ ∧ InvariantsHold current clauses
  let G : Bool → Env → Prop := fun test current =>
    LocalState.Frozen Γ entry current ∧ LocalState.EnvTyped current Γ ∧
    ∃ out ∈ conditionResult.outcomes, ∃ extended,
      AgreeBelow start model extended ∧ out.path.Holds extended ∧
      Denotes extended out.value (.bool test) ∧ EnvRep extended out.env current
  have initialInvariant : I entry := by
    have initialValid : ValidFrom start model initial :=
      valid_subset accepted (fun _ hm => List.mem_append_left _ hm)
    exact ⟨LocalState.frozen_refl entryTyped, entryTyped,
      assertions_established hi hentry (initialValid model agree_refl) entryPath⟩
  have conditionSpec : ∀ current, I current → EvalSpec fs condition current
      (fun value final => ∃ test, value = .bool test ∧ G test final) := by
    intro current hI
    obtain ⟨frozen, typed, established⟩ := hI
    obtain ⟨_, _, extended, hext, hhead, hdomain⟩ := fresh_head_coverage hh hs hentry frozen typed
    have hheadInv := (assertions_truth hinv hhead).mpr established
    have hentryPath := (formula_agree hpath hext).mp entryPath
    have hvalid := valid_extend conditionValid hext hn
    apply spec_mono (spec_frame
      (cs extended current hhead typed ⟨hentryPath, hdomain, hheadInv⟩ hvalid) wf htc typed)
    intro value final hout
    obtain ⟨covered, hframe, htyped, hvalue⟩ := hout
    cases value with
    | int _ | unit => simp [Val.type] at hvalue
    | bool test =>
      obtain ⟨out, hm, finalModel, ha, hp, hv, he⟩ := covered
      exact ⟨test, rfl, LocalState.frozen_trans frozen hframe, htyped, out, hm,
        finalModel, agree_trans hext (agree_restrict ha hn), hp, hv, he⟩
  have bodySpec : ∀ current, G true current → EvalSpec fs body current
      (fun value final => value = .unit ∧ I final) := by
    intro current hG
    obtain ⟨frozen, typed, out, hm, currentModel, hext, hp, hv, he⟩ := hG
    obtain ⟨next, result, hnext, hresult, _, hchecks⟩ :=
      bind_locate (fun _ _ _ h => action_counter gc h) hg hm
    have bounds := cb out hm
    have envBound := symbols_below_mono bounds.2.1 hnext
    have pathBound : FormulaBelow next (.and out.path (.holds out.value)) :=
      ⟨formula_bound_mono bounds.2.2 hnext, below_mono bounds.1 hnext⟩
    have actionValid := valid_extend (valid_subset iterationValid hchecks) hext
      (Nat.le_trans htotal hnext)
    simp only [loopAction, bind, Option.bind_eq_some_iff, Option.pure_def] at hresult
    obtain ⟨bodyResult, hbody, preservation, hpreserve, heq⟩ := hresult
    cases heq
    have preservationValid : ValidFrom next currentModel preservation.checks :=
      valid_subset actionValid (fun _ hm => List.mem_cons_of_mem _ hm)
    have bodyValid := valid_subset preservationValid (bind_input_checks hpreserve)
    apply spec_mono (spec_frame
      (gs _ _ _ _ hbody envBound pathBound currentModel current he typed ⟨hp, hv⟩ bodyValid)
      wf htb typed)
    intro value final hout
    obtain ⟨covered, hframe, htyped, hvalue⟩ := hout
    obtain ⟨last, lastNext, lastResult, lastModel, _, _, hlast, _, hlastPath, _, hlastEnv,
      _, _, _, lastValid, _⟩ := bind_context (fun _ _ _ h => preserve_counter h) hpreserve
        (gc _ _ _ _ hbody) (gb _ _ _ _ hbody envBound pathBound) preservationValid covered
    simp only [preserveAction, bind, Option.bind_eq_some_iff, Option.pure_def] at hlast
    obtain ⟨⟨checks, truth⟩, hass, heq⟩ := hlast
    cases heq
    have inv := assertions_established hass hlastEnv (lastValid lastModel agree_refl) hlastPath
    have hf := LocalState.frozen_trans frozen hframe
    cases value with
    | int _ | bool _ => simp [Val.type] at hvalue
    | unit => exact ⟨rfl, hf, htyped, inv⟩
  apply spec_mono (invariant_loop_rule conditionSpec bodySpec initialInvariant)
  intro value final hout
  obtain ⟨rfl, _, _, out, hm, finalModel, hext, hp, hv, he⟩ := hout
  obtain ⟨next, result, _, hresult, houts, _⟩ :=
    bind_locate (fun _ _ _ h => action_counter gc h) hg hm
  exact ⟨falseOutcome out, houts _ (action_false hresult), finalModel, hext,
    ⟨hp, false_guard hv⟩, rfl, he⟩

end APL.LoopVCG

namespace APL.LoopVCG

open VCG
open LocalState.LoopVerification

def ArgsCovered (bound : Nat) (model : Model) (analysis : Analysis (List SymTerm))
    (values : Env) (env : Env) : Prop :=
  ∃ outcome ∈ analysis.outcomes, ∃ extended,
    AgreeBelow bound model extended ∧ outcome.path.Holds extended ∧
      EnvRep extended outcome.value values ∧ EnvRep extended outcome.env env

theorem args_spec_mono
    (h : ArgsSpec fs args env result)
    (weaken : ∀ values final, result values final → result' values final) :
    ArgsSpec fs args env result' := by
  induction args generalizing env result result' with
  | nil => exact weaken [] env h
  | cons arg rest ih =>
    apply spec_mono h
    intro value current hrest
    exact ih hrest (fun values final => weaken (value :: values) final)

theorem arguments_analysis_sound
    (wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions fs))
    (child : ∀ {Γ e ty syms path start generated},
      LocalState.HasType (LocalState.signatures (LoopAnnotations.eraseFunctions fs)) Γ e.erase ty →
      analyze fs preconditions height Γ e syms path start = some generated →
      SymbolsBelow start syms → FormulaBelow start path →
      SoundAt (LoopAnnotations.eraseFunctions fs) e.erase Γ syms path start generated)
    (ht : LocalState.ArgsTyped (LocalState.signatures (LoopAnnotations.eraseFunctions fs))
      Γ (args.map LoopAnnotations.Term.erase) types)
    (hg : arguments (analyze fs preconditions height Γ) args syms path start = some generated)
    (he : SymbolsBelow start syms) (hp : FormulaBelow start path)
    (henv : EnvRep model syms env) (htyped : LocalState.EnvTyped env Γ)
    (hpath : path.Holds model) (hvalid : ValidFrom start model generated.checks) :
    ArgsSpec (LoopAnnotations.eraseFunctions fs) (args.map LoopAnnotations.Term.erase) env
      (fun values final => ArgsCovered start model generated values final ∧
        values.map Val.type = types ∧ LocalState.EnvTyped final Γ) := by
  induction args generalizing types syms path start generated model env with
  | nil =>
    cases ht
    cases hg
    exact ⟨⟨⟨[], syms, path⟩, by simp [single], model, agree_refl, hpath, .nil, henv⟩,
      rfl, htyped⟩
  | cons arg rest ih =>
    cases ht with
    | cons harg hrest =>
      simp only [arguments, bind, Option.bind_eq_some_iff] at hg
      obtain ⟨first, hf, hbind⟩ := hg
      have cf := child harg hf he hp model env henv htyped hpath
        (valid_subset hvalid (bind_input_checks hbind))
      have framed := spec_frame cf wf harg htyped
      apply spec_mono framed
      intro value current hout
      obtain ⟨covered, _, currentTyped, valueTyped⟩ := hout
      obtain ⟨out, hm, extended, oldAgree, outPath, outValue, outEnv⟩ := covered
      have bounds := (analyze_supported hf he hp).1 out hm
      have counter : ∀ (out : Outcome SymTerm) (next : Nat) (result : Analysis (List SymTerm)),
          (do
            let remaining ← arguments (analyze fs preconditions height Γ) rest out.env out.path next
            return { remaining with outcomes := remaining.outcomes.map fun r =>
              ⟨out.value :: r.value, r.env, r.path⟩ }) = some result → next ≤ result.next := by
        intro out next result haction
        simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at haction
        obtain ⟨remaining, hr, heq⟩ := haction
        cases heq
        exact arguments_counter (generate := analyze fs preconditions height Γ)
          (generated := remaining) (fun _ _ _ _ _ h => analyze_counter h) hr
      obtain ⟨next, action, nextBound, haction, outputSubset, checkSubset⟩ :=
        bind_locate counter hbind hm
      simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at haction
      obtain ⟨remaining, hr, heq⟩ := haction
      cases heq
      have startBound := Nat.le_trans (analyze_counter hf) nextBound
      have envBound := symbols_below_mono bounds.2.1 nextBound
      have pathBound := formula_bound_mono bounds.2.2 nextBound
      have tailValid : ValidFrom next extended remaining.checks :=
        valid_extend (valid_subset hvalid checkSubset) oldAgree startBound
      have tail := ih hrest hr envBound pathBound outEnv currentTyped outPath tailValid
      apply args_spec_mono tail
      intro values final htail
      obtain ⟨⟨tailOut, tailMember, finalModel, laterAgree, finalPath, finalValues, finalEnv⟩,
        valuesTyped, finalTyped⟩ := htail
      have captured := denotes_agree (below_mono bounds.1 nextBound) laterAgree outValue
      refine ⟨?_, ?_, finalTyped⟩
      · refine ⟨⟨out.value :: tailOut.value, tailOut.env, tailOut.path⟩,
          outputSubset _ (List.mem_map.mpr ⟨tailOut, tailMember, rfl⟩), finalModel,
          agree_trans oldAgree (agree_restrict laterAgree startBound), finalPath,
          .cons captured finalValues, finalEnv⟩
      · simp only [List.map_cons, valueTyped, valuesTyped]

theorem call_analysis_sound
    (wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions fs))
    (child : ∀ {Γ e ty syms path start generated},
      LocalState.HasType (LocalState.signatures (LoopAnnotations.eraseFunctions fs)) Γ e.erase ty →
      analyze fs preconditions height Γ e syms path start = some generated →
      SymbolsBelow start syms → FormulaBelow start path →
      SoundAt (LoopAnnotations.eraseFunctions fs) e.erase Γ syms path start generated)
    (ht : LocalState.HasType (LocalState.signatures (LoopAnnotations.eraseFunctions fs)) Γ
      (.call function (args.map LoopAnnotations.Term.erase)) ty)
    (hg : analyze fs preconditions (height + 1) Γ (.call function args) syms path start = some generated)
    (he : SymbolsBelow start syms) (hp : FormulaBelow start path) :
    SoundAt (LoopAnnotations.eraseFunctions fs)
      (.call function (args.map LoopAnnotations.Term.erase)) Γ syms path start generated := by
  simp only [analyze, bind, Option.bind_eq_some_iff] at hg
  obtain ⟨_, _, actuals, hargs, hbind⟩ := hg
  intro model env henv htyped hpath hvalid
  cases ht with
  | call hsig htargs =>
    have argumentsSound := arguments_analysis_sound wf child htargs hargs he hp henv htyped hpath
      (valid_subset hvalid (bind_input_checks hbind))
    apply call_rule
    apply args_spec_mono argumentsSound
    intro values caller hresults
    obtain ⟨⟨out, hm, extended, oldAgree, outPath, outValues, outCaller⟩, valuesTyped, _⟩ := hresults
    have argsBounds := arguments_supported
      (generate := analyze fs preconditions height Γ)
      (fun _ _ _ _ _ he hp hg => ⟨analyze_counter hg, analyze_supported hg he hp⟩) he hp hargs
    have bounds := argsBounds.2.1 out hm
    have counter : ∀ (out : Outcome (List SymTerm)) (next : Nat) (result : Analysis SymTerm),
        (do
          let fn ← fs[function]?
          if out.value.length = fn.params.length then
            let (defined, truth) ← requiresVC out.value (preconditions function)
            let body ← analyze fs preconditions height (LocalState.immutable fn.params.reverse)
              fn.body out.value.reverse out.path next
            return addCheck out.path (.and defined truth)
              { body with outcomes := body.outcomes.map fun result => { result with env := out.env } }
          else none) = some result → next ≤ result.next := by
      intro out next result haction
      simp only [bind, Option.bind_eq_some_iff] at haction
      obtain ⟨fn, _, hbody⟩ := haction
      split at hbody
      next =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at hbody
        obtain ⟨⟨_, _⟩, _, body, hb, heq⟩ := hbody
        cases heq
        exact analyze_counter (generated := body) hb
      next => contradiction
    obtain ⟨next, action, nextBound, haction, outputSubset, checkSubset⟩ := bind_locate counter hbind hm
    simp only [bind, Option.bind_eq_some_iff] at haction
    obtain ⟨fn, hfn, hbody⟩ := haction
    split at hbody
    next =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hbody
      obtain ⟨⟨defined, truth⟩, hpre, body, hb, heq⟩ := hbody
      cases heq
      have startBound := Nat.le_trans argsBounds.1 nextBound
      have inputBound := symbols_below_mono bounds.1 nextBound
      have callerBound := symbols_below_mono bounds.2.1 nextBound
      have pathBound := formula_bound_mono bounds.2.2 nextBound
      have bodyValid : ValidFrom next extended body.checks :=
        valid_extend (valid_subset hvalid (fun check hm =>
          checkSubset check (List.mem_cons_of_mem _ hm))) oldAgree startBound
      have fnLookup : (LoopAnnotations.eraseFunctions fs)[function]? = some fn.erase := by
        simp only [LoopAnnotations.eraseFunctions, Array.getElem?_map, hfn, Option.map_some]
      have signature := LocalState.signatures_lookup fnLookup
      have same := Option.some.inj (hsig.symm.trans signature)
      have paramsSame := (Prod.mk.inj same).1
      have argumentTypes : values.map Val.type = fn.params := valuesTyped.trans paramsSame
      have bodyType := wf function fn.erase fnLookup
      have inputTyped : LocalState.EnvTyped values.reverse (LocalState.immutable fn.params.reverse) := by
        simp [LocalState.EnvTyped, LocalState.immutable, List.map_reverse, List.map_map,
          Function.comp_def, argumentTypes]
      have bodySpec := child bodyType hb (symbols_reverse inputBound) pathBound
        extended values.reverse (VCG.env_reverse outValues) inputTyped outPath bodyValid
      refine ⟨fn.erase, fnLookup, ?_⟩
      apply spec_mono bodySpec
      intro value final covered
      obtain ⟨bodyOut, bodyMember, finalModel, laterAgree, finalPath, finalValue, _⟩ := covered
      have savedCaller := env_agree callerBound laterAgree outCaller
      exact ⟨{ bodyOut with env := out.env },
        outputSubset _ (List.mem_map.mpr ⟨bodyOut, bodyMember, rfl⟩), finalModel,
        agree_trans oldAgree (agree_restrict laterAgree startBound), finalPath, finalValue, savedCaller⟩
    next => contradiction

theorem callee_requires_defined_and_true {analysis : Analysis SymTerm}
    (hg : requiresVC syms clauses = some (defined, truth))
    (hv : ValidFrom bound model (addCheck path (.and defined truth) analysis).checks)
    (hp : path.Holds model) (he : EnvRep model syms values) :
    RequiresDefined (values.map embed) clauses ∧ RequiresHold (values.map embed) clauses := by
  have checked : (Formula.and defined truth).Holds model :=
    valid_member hv (check := ⟨path, .and defined truth⟩) (by simp [addCheck]) agree_refl hp
  exact ⟨(requires_vc_sound hg he).1.mp checked.1, (requires_vc_sound hg he).2.mp checked.2⟩

end APL.LoopVCG

namespace APL.LoopVCG

open VCG
open LocalState.LoopVerification

theorem analyze_sound
    (wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions fs))
    (hg : analyze fs preconditions height Γ e syms path start = some generated)
    (he : SymbolsBelow start syms) (hp : FormulaBelow start path) :
    SoundAt (LoopAnnotations.eraseFunctions fs) e.erase Γ syms path start generated := by
  induction height generalizing Γ e syms path start generated with
  | zero => simp [analyze] at hg
  | succ height ih =>
    have original := hg
    simp only [analyze, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨ty, inferred, hg⟩ := hg
    have typed : LocalState.HasType (LocalState.signatures (LoopAnnotations.eraseFunctions fs)) Γ e.erase ty := by
      rw [LoopAnnotations.erase_signatures]
      exact LocalState.infer_sound inferred
    cases e with
    | lit value =>
      simp only [LoopAnnotations.Term.erase] at typed ⊢
      cases hg
      exact literal_sound
    | «local» index =>
      simp only [LoopAnnotations.Term.erase] at typed ⊢
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨symbol, hs, heq⟩ := hg
      cases heq
      exact local_sound hs
    | letE a b =>
      simp only [LoopAnnotations.Term.erase] at typed ⊢
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨initTy, htype, first, hfirst, hbind⟩ := hg
      have initialTyped : LocalState.HasType (LocalState.signatures (LoopAnnotations.eraseFunctions fs)) Γ a.erase initTy := by
        rw [LoopAnnotations.erase_signatures]
        exact LocalState.infer_sound htype
      exact binding_analysis_sound (permission := false)
        (generate := analyze fs preconditions height ((initTy, false) :: Γ) b)
        wf initialTyped (ih hfirst he hp) (analyze_counter hfirst)
        (analyze_supported hfirst he hp).1
        (fun _ _ _ _ h => analyze_counter h)
        (fun _ _ _ _ h hb hf => ih h hb hf) hbind
    | letMut a b =>
      simp only [LoopAnnotations.Term.erase] at typed ⊢
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨initTy, htype, first, hfirst, hbind⟩ := hg
      have initialTyped : LocalState.HasType (LocalState.signatures (LoopAnnotations.eraseFunctions fs)) Γ a.erase initTy := by
        rw [LoopAnnotations.erase_signatures]
        exact LocalState.infer_sound htype
      exact binding_analysis_sound (permission := true)
        (generate := analyze fs preconditions height ((initTy, true) :: Γ) b)
        wf initialTyped (ih hfirst he hp) (analyze_counter hfirst)
        (analyze_supported hfirst he hp).1
        (fun _ _ _ _ h => analyze_counter h)
        (fun _ _ _ _ h hb hf => ih h hb hf) hbind
    | assign index rhs =>
      simp only [LoopAnnotations.Term.erase] at typed ⊢
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨first, hfirst, hbind⟩ := hg
      exact assignment_analysis_sound (ih hfirst he hp) (analyze_counter hfirst)
        (analyze_supported hfirst he hp).1 hbind
    | ifE condition yes no =>
      simp only [LoopAnnotations.Term.erase] at typed ⊢
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨first, hfirst, hbind⟩ := hg
      cases typed with
      | ifE conditionTyped _ _ =>
        exact conditional_analysis_sound wf conditionTyped (ih hfirst he hp)
          (analyze_counter hfirst) (analyze_supported hfirst he hp).1
          (fun h hb hf => ih h hb hf) hbind
    | unary op arg =>
      simp only [LoopAnnotations.Term.erase] at typed ⊢
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨first, hfirst, hbind⟩ := hg
      exact unary_analysis_sound (ih hfirst he hp) (analyze_counter hfirst)
        (analyze_supported hfirst he hp).1 hbind
    | binary op left right =>
      simp only [LoopAnnotations.Term.erase] at typed ⊢
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨first, hfirst, hbind⟩ := hg
      cases typed with
      | binary leftTyped _ _ =>
        exact binary_analysis_sound wf leftTyped (ih hfirst he hp)
          (analyze_counter hfirst) (analyze_supported hfirst he hp).1
          (fun h hb hf => ih h hb hf)
          (fun h hb hf => (analyze_supported h hb hf).1) hbind
    | call function args =>
      simp only [LoopAnnotations.Term.erase] at typed ⊢
      exact call_analysis_sound wf (fun _ h hb hf => ih h hb hf) typed original he hp
    | whileE clauses condition body =>
      simp only [LoopAnnotations.Term.erase] at typed ⊢
      simp only [] at hg
      split at hg
      next => contradiction
      next =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
        obtain ⟨⟨initial, initialTruth⟩, hi, head, hh, ⟨headChecks, invariant⟩, hinv,
          conditionResult, hc, iterations, hit, heq⟩ := hg
        cases heq
        obtain ⟨nh, sh, dh⟩ := fresh_head_bounded hh he
        have invBound := (assertions_bounded hinv sh (formula_bound_mono hp nh)).2
        have headPathBound : FormulaBelow head.next (.and path (.and head.domain invariant)) :=
          ⟨formula_bound_mono hp nh, dh, invBound⟩
        cases typed with
        | whileE conditionTyped bodyTyped =>
          exact loop_analysis_sound
            (generate := analyze fs preconditions height Γ body)
            wf conditionTyped bodyTyped he hp hi hh hinv (ih hc sh headPathBound)
            (analyze_counter hc) (analyze_supported hc sh headPathBound).1
            (fun _ _ _ _ h => analyze_counter h)
            (fun _ _ _ _ h hb hf => ih h hb hf)
            (fun _ _ _ _ h hb hf => (analyze_supported h hb hf).1) hit

theorem analyze_run_sound
    (wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions fs))
    (hg : analyze fs preconditions height Γ e syms path start = some generated)
    (he : SymbolsBelow start syms) (hp : FormulaBelow start path)
    (henv : EnvRep model syms env) (htyped : LocalState.EnvTyped env Γ)
    (hpath : path.Holds model) (hvalid : ValidFrom start model generated.checks) :
    StateVCG.RunSafe (Covered start model generated)
      (LocalState.run (LoopAnnotations.eraseFunctions fs) budget (.eval e.erase env [])) :=
  closed_run (analyze_sound wf hg he hp model env henv htyped hpath hvalid)

theorem analyze_steps_no_trap
    (wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions fs))
    (hg : analyze fs preconditions height Γ e syms path start = some generated)
    (he : SymbolsBelow start syms) (hp : FormulaBelow start path)
    (henv : EnvRep model syms env) (htyped : LocalState.EnvTyped env Γ)
    (hpath : path.Holds model) (hvalid : ValidFrom start model generated.checks) :
    ¬ LocalState.Steps (LoopAnnotations.eraseFunctions fs) (.eval e.erase env []) (.trap kind) :=
  no_finite_trap (analyze_sound wf hg he hp model env henv htyped hpath hvalid)

theorem analyze_steps_no_invalid
    (wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions fs))
    (hg : analyze fs preconditions height Γ e syms path start = some generated)
    (he : SymbolsBelow start syms) (hp : FormulaBelow start path)
    (henv : EnvRep model syms env) (htyped : LocalState.EnvTyped env Γ)
    (hpath : path.Holds model) (hvalid : ValidFrom start model generated.checks) :
    ¬ LocalState.Steps (LoopAnnotations.eraseFunctions fs) (.eval e.erase env []) .invalid :=
  no_finite_invalid (analyze_sound wf hg he hp model env henv htyped hpath hvalid)

theorem analyze_steps_value
    (wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions fs))
    (hg : analyze fs preconditions height Γ e syms path start = some generated)
    (he : SymbolsBelow start syms) (hp : FormulaBelow start path)
    (henv : EnvRep model syms env) (htyped : LocalState.EnvTyped env Γ)
    (hpath : path.Holds model) (hvalid : ValidFrom start model generated.checks)
    (trace : LocalState.Steps (LoopAnnotations.eraseFunctions fs)
      (.eval e.erase env []) (.ret value final [])) : Covered start model generated value final := by
  obtain ⟨budget, hr⟩ := LocalState.run_complete trace rfl
  have safe := analyze_run_sound (budget := budget) wf hg he hp henv htyped hpath hvalid
  simpa only [hr, StateVCG.RunSafe] using safe

end APL.LoopVCG
