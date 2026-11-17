import APL.LoopVCG

/-! Symbol support for every generated outcome and guarded check. Together
with counter monotonicity this separates existing artifacts from subsequent
fresh heads; it does not record a global allocation-event manifest. -/

namespace APL.LoopVCG

open VCG LoopAnnotations

theorem lookup_bounded {i : Nat} (h : SymbolsBelow n syms) (hi : syms[i]? = some s) : Below n s := by
  induction syms generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero => cases hi; exact h.1
    | succ i => exact ih h.2 hi

theorem assertion_bounded {a : Assertion} (h : a.instantiate syms = some s)
    (hb : SymbolsBelow n syms) : Below n s := by
  induction a generalizing s with
  | lit v => cases h; trivial
  | «local» i => exact lookup_bounded hb h
  | unary op a ih =>
    simp only [Assertion.instantiate, Assertion.toSpec, Spec.instantiate, bind,
      Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨x, hx, heq⟩ := h
    cases heq
    change Below n x
    exact ih hx
  | binary op a b ia ib =>
    simp only [Assertion.instantiate, Assertion.toSpec, Spec.instantiate, bind,
      Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨x, hx, y, hy, heq⟩ := h
    cases heq
    exact ⟨ia hx, ib hy⟩

theorem formula_bound_mono (hf : FormulaBelow n formula) (hn : n ≤ m) :
    FormulaBelow m formula := by
  induction formula with
  | truth _ => trivial
  | holds s | defined s | boolean s | range s => exact below_mono hf hn
  | and a b ia ib | imp a b ia ib => exact ⟨ia hf.1, ib hf.2⟩
  | not a ih => exact ih hf

theorem type_guard_bounded (h : Below n s) : FormulaBelow n (typeGuard ty s) := by
  cases ty with
  | i64 | bool => exact h
  | unit => exact ⟨h, trivial⟩

theorem domain_bounded (hg : headDomain Γ syms = some domain)
    (hb : SymbolsBelow n syms) : FormulaBelow n domain := by
  induction Γ generalizing syms domain with
  | nil =>
    cases syms with
    | nil => cases hg; trivial
    | cons _ _ => simp [headDomain] at hg
  | cons binding Γ ih =>
    cases syms with
    | nil => simp [headDomain] at hg
    | cons s rest =>
      cases binding
      simp only [headDomain, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨tail, ht, heq⟩ := hg
      cases heq
      exact ⟨type_guard_bounded hb.1, ih ht hb.2⟩

theorem fresh_head_bounded (hg : freshHead Γ syms next = some head)
    (hb : SymbolsBelow next syms) : next ≤ head.next ∧
      SymbolsBelow head.next head.symbols ∧ FormulaBelow head.next head.domain := by
  simp only [freshHead, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨⟨symbols, final⟩, hfresh, domain, hdomain, heq⟩ := hg
  cases heq
  obtain ⟨hn, hsymbols⟩ := fresh_bounded hfresh hb
  exact ⟨hn, hsymbols, domain_bounded hdomain hsymbols⟩

end APL.LoopVCG

namespace APL.LoopVCG

open VCG

def OutcomeBelow (P : Nat → α → Prop) (n : Nat) (out : Outcome α) : Prop :=
  P n out.value ∧ SymbolsBelow n out.env ∧ FormulaBelow n out.path

def ChecksBelow (n : Nat) (checks : List Check) : Prop :=
  ∀ check ∈ checks, FormulaBelow n check.guard ∧ FormulaBelow n check.required

def Supported (P : Nat → α → Prop) (analysis : Analysis α) : Prop :=
  (∀ out ∈ analysis.outcomes, OutcomeBelow P analysis.next out) ∧
    ChecksBelow analysis.next analysis.checks

def BoundMono (P : Nat → α → Prop) : Prop := ∀ {n m value}, n ≤ m → P n value → P m value

theorem term_mono : BoundMono Below := fun h x => below_mono x h
theorem symbols_mono : BoundMono SymbolsBelow := fun h x => symbols_below_mono x h

theorem outcome_mono (hp : BoundMono P) (hn : n ≤ m) (h : OutcomeBelow P n out) :
    OutcomeBelow P m out :=
  ⟨hp hn h.1, symbols_below_mono h.2.1 hn, formula_bound_mono h.2.2 hn⟩

theorem checks_mono (hn : n ≤ m) (h : ChecksBelow n checks) : ChecksBelow m checks := by
  intro check hc
  exact ⟨formula_bound_mono (h check hc).1 hn, formula_bound_mono (h check hc).2 hn⟩

theorem checks_append (ha : ChecksBelow n a) (hb : ChecksBelow n b) : ChecksBelow n (a ++ b) := by
  intro check hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ha check hc
  · exact hb check hc

theorem combine_supported (hp : BoundMono P) (hnext : a.next ≤ b.next)
    (ha : Supported P a) (hb : Supported P b) : Supported P (combine a b) := by
  constructor
  · intro out ho
    rcases List.mem_append.mp ho with ho | ho
    · exact outcome_mono hp hnext (ha.1 out ho)
    · exact hb.1 out ho
  · exact checks_append (checks_mono hnext ha.2) hb.2

theorem single_supported (hv : P n value) (he : SymbolsBelow n env) (hf : FormulaBelow n path) :
    Supported P (single value env path n) := by
  constructor
  · intro out ho
    simp only [single, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst out
    exact ⟨hv, he, hf⟩
  · intro check hc; cases hc

theorem add_check_supported {guard : Formula} (h : Supported P a) (hg : FormulaBelow a.next guard)
    (hr : FormulaBelow a.next required) : Supported P (addCheck guard required a) := by
  refine ⟨h.1, ?_⟩
  intro check hc
  rcases List.mem_cons.mp hc with heq | hc
  · subst check; exact ⟨hg, hr⟩
  · exact h.2 check hc

theorem sequence_supported {P : Nat → α → Prop} {Q : Nat → β → Prop}
    {action : Outcome α → Nat → Option (Analysis β)}
    (pm : BoundMono P) (qm : BoundMono Q)
    (ha : ∀ out start generated, lower ≤ start → OutcomeBelow P start out →
      action out start = some generated → start ≤ generated.next ∧ Supported Q generated)
    (hl : lower ≤ start) (hi : ∀ out ∈ outcomes, OutcomeBelow P start out)
    (hg : sequence action outcomes start = some generated) :
    start ≤ generated.next ∧ Supported Q generated := by
  induction outcomes generalizing start generated with
  | nil =>
    cases hg
    exact ⟨Nat.le_refl _, (by intro out ho; cases ho), (by intro check hc; cases hc)⟩
  | cons out rest ih =>
    simp only [sequence, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, hf, tail, ht, heq⟩ := hg
    cases heq
    obtain ⟨hn, hs⟩ := ha out start first hl (hi out (by simp)) hf
    obtain ⟨htn, hts⟩ := ih (Nat.le_trans hl hn)
      (fun item hm => outcome_mono pm hn (hi item (List.mem_cons_of_mem _ hm))) ht
    exact ⟨Nat.le_trans hn htn, combine_supported qm htn hs hts⟩

theorem bind_supported {P : Nat → α → Prop} {Q : Nat → β → Prop}
    {input : Analysis α} {action : Outcome α → Nat → Option (Analysis β)}
    (pm : BoundMono P) (qm : BoundMono Q) (hi : Supported P input)
    (ha : ∀ out start generated, input.next ≤ start → OutcomeBelow P start out →
      action out start = some generated → start ≤ generated.next ∧ Supported Q generated)
    (hg : bindAnalysis input action = some generated) :
    input.next ≤ generated.next ∧ Supported Q generated := by
  simp only [bindAnalysis, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨later, hl, heq⟩ := hg
  cases heq
  obtain ⟨hn, hs⟩ := sequence_supported (P := P) (Q := Q) pm qm ha (Nat.le_refl _) hi.1 hl
  exact ⟨hn, hs.1, checks_append (checks_mono hn hi.2) hs.2⟩

theorem symbols_mem (h : SymbolsBelow n syms) : ∀ s ∈ syms, Below n s := by
  induction syms with
  | nil => simp
  | cons a rest ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h.1
    · exact ih h.2 s hs

theorem symbols_of_mem (h : ∀ s ∈ syms, Below n s) : SymbolsBelow n syms := by
  induction syms with
  | nil => trivial
  | cons a rest ih => exact ⟨h a (by simp), ih (fun s hs => h s (List.mem_cons_of_mem _ hs))⟩

theorem symbols_reverse (h : SymbolsBelow n syms) : SymbolsBelow n syms.reverse := by
  apply symbols_of_mem
  intro s hs
  exact symbols_mem h s (List.mem_reverse.mp hs)

theorem symbols_tail (h : SymbolsBelow n syms) : SymbolsBelow n syms.tail := by
  cases syms with
  | nil => trivial
  | cons a rest => exact h.2

theorem update_bounded (h : StateVCG.updateSymbols syms i value = some updated)
    (he : SymbolsBelow n syms) (hv : Below n value) : SymbolsBelow n updated := by
  induction syms generalizing i updated with
  | nil => simp [StateVCG.updateSymbols] at h
  | cons a rest ih =>
    cases i with
    | zero => cases h; exact ⟨hv, he.2⟩
    | succ i =>
      simp only [StateVCG.updateSymbols, Option.map_eq_some_iff] at h
      obtain ⟨tail, ht, rfl⟩ := h
      exact ⟨he.1, ih ht he.2⟩

theorem spec_bounded {spec : Spec} (h : spec.instantiate syms result = some s)
    (he : SymbolsBelow n syms) (hr : ∀ value, result = some value → Below n value) : Below n s := by
  induction spec generalizing s with
  | lit value => cases h; trivial
  | param i => exact lookup_bounded he h
  | result => exact hr s h
  | unary op a ih =>
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨term, ht, heq⟩ := h
    cases heq
    change Below n term
    exact ih ht
  | binary op a b ia ib =>
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨left, hl, right, hr, heq⟩ := h
    cases heq
    exact ⟨ia hl, ib hr⟩

theorem requires_bounded (h : requiresVC syms clauses = some (defined, truth))
    (he : SymbolsBelow n syms) : FormulaBelow n defined ∧ FormulaBelow n truth := by
  induction clauses generalizing defined truth with
  | nil => cases h; exact ⟨trivial, trivial⟩
  | cons clause rest ih =>
    simp only [requiresVC, bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨term, ht, ⟨defined, truth⟩, hr, heq⟩ := h
    cases heq
    have hs := spec_bounded ht he (by intro value impossible; cases impossible)
    obtain ⟨hd, htruth⟩ := ih hr
    exact ⟨⟨hs, hs, hd⟩, hs, htruth⟩

theorem assertions_bounded (h : assertions syms path clauses = some (checks, truth))
    (he : SymbolsBelow n syms) (hp : FormulaBelow n path) :
    ChecksBelow n checks ∧ FormulaBelow n truth := by
  induction clauses generalizing checks truth with
  | nil => cases h; exact ⟨(by intro check hc; cases hc), trivial⟩
  | cons clause rest ih =>
    simp only [assertions, bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨term, ht, ⟨checks, truth⟩, hr, heq⟩ := h
    cases heq
    have hs := assertion_bounded ht he
    obtain ⟨hc, htruth⟩ := ih hr
    constructor
    · intro check hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨hp, hs, hs⟩
      · exact hc check hm
    · exact ⟨⟨hs, hs⟩, htruth⟩

theorem unary_guard_bounded (h : Below n value) : FormulaBelow n (unaryGuard op value) := by
  cases op <;> exact h

theorem division_guard_bounded (ha : Below n a) (hb : Below n b) :
    FormulaBelow n (divisionGuard a b) := ⟨⟨hb, trivial⟩, ⟨ha, trivial⟩, hb, trivial⟩

theorem binary_guard_bounded (ha : Below n a) (hb : Below n b) :
    FormulaBelow n (binaryGuard op a b) := by
  cases op <;> try exact ⟨ha, hb⟩
  all_goals exact ⟨division_guard_bounded ha hb, ha, hb⟩

theorem short_guard_bounded (h : Below n value) : FormulaBelow n (shortGuard op value) := by
  cases op <;> trivial

theorem map_outcomes_supported {f : Outcome α → Outcome β}
    (h : Supported P a)
    (hf : ∀ out, OutcomeBelow P a.next out → OutcomeBelow Q a.next (f out)) :
    Supported Q { a with outcomes := a.outcomes.map f } := by
  refine ⟨?_, h.2⟩
  intro out ho
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp ho
  exact hf old (h.1 old hm)

theorem mapM_property {f : α → Option β} {P : α → Prop} {Q : β → Prop}
    {input : List α} {output : List β}
    (hf : ∀ a b, P a → f a = some b → Q b)
    (hi : ∀ a ∈ input, P a) (hg : input.mapM f = some output) :
    ∀ b ∈ output, Q b := by
  induction input generalizing output with
  | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hg; subst output; simp
  | cons a rest ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨b, hb, tail, ht, heq⟩ := hg
    cases heq
    intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hf a _ (hi a (by simp)) hb
    · exact ih (fun item hm => hi item (List.mem_cons_of_mem _ hm)) ht value hv

theorem scope_supported (ha : Supported Below a)
    (hg : a.outcomes.mapM (fun result => do
      let _ ← result.env.head?
      return { result with env := result.env.tail }) = some outputs) :
    Supported Below { a with outcomes := outputs } := by
  refine ⟨?_, ha.2⟩
  apply mapM_property (Q := OutcomeBelow Below a.next) (hi := ha.1) (hg := hg)
  intro before after hb hmap
  simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at hmap
  obtain ⟨_, _, heq⟩ := hmap
  cases heq
  exact ⟨hb.1, symbols_tail hb.2.1, hb.2.2⟩

theorem arguments_supported
    {generate : LoopAnnotations.Term → List SymTerm → Formula → Nat → Option (Analysis SymTerm)}
    (ha : ∀ e env path start generated, SymbolsBelow start env → FormulaBelow start path →
      generate e env path start = some generated → start ≤ generated.next ∧ Supported Below generated)
    (he : SymbolsBelow start env) (hp : FormulaBelow start path)
    (hg : arguments generate args env path start = some generated) :
    start ≤ generated.next ∧ Supported SymbolsBelow generated := by
  induction args generalizing env path start generated with
  | nil => cases hg; exact ⟨Nat.le_refl _, single_supported trivial he hp⟩
  | cons arg rest ih =>
    simp only [arguments, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨first, hf, hlater⟩ := hg
    obtain ⟨hn, hs⟩ := ha arg env path start first he hp hf
    obtain ⟨hnext, hfinal⟩ := bind_supported (P := Below) (Q := SymbolsBelow)
      term_mono symbols_mono hs (hg := hlater) (by
        intro out next output _ hout haction
        simp only [Option.bind_eq_some_iff, Option.pure_def] at haction
        obtain ⟨remaining, hr, heq⟩ := haction
        cases heq
        obtain ⟨hrn, hrs⟩ := ih hout.2.1 hout.2.2 hr
        refine ⟨hrn, map_outcomes_supported hrs ?_⟩
        intro r hbound
        exact ⟨⟨below_mono hout.1 hrn, hbound.1⟩, hbound.2⟩)
    exact ⟨Nat.le_trans hn hnext, hfinal⟩

theorem analyze_supported
    (hg : analyze fs preconditions height Γ e env path start = some generated)
    (he : SymbolsBelow start env) (hp : FormulaBelow start path) : Supported Below generated := by
  induction height generalizing Γ e env path start generated with
  | zero => simp [analyze] at hg
  | succ height ih =>
    simp only [analyze, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨ty, hinfer, hg⟩ := hg
    cases e with
    | lit value => cases hg; exact single_supported trivial he hp
    | «local» i =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨symbol, hs, heq⟩ := hg
      cases heq
      exact single_supported (lookup_bounded he hs) he hp
    | letE a b | letMut a b =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨ty, ht, first, hf, hbody⟩ := hg
      apply (bind_supported (P := Below) (Q := Below) term_mono term_mono (ih hf he hp) ?_ hbody).2
      intro out next output _ hout haction
      simp only [Option.bind_eq_some_iff, Option.pure_def] at haction
      obtain ⟨body, hb, results, hscope, heq⟩ := haction
      cases heq
      exact ⟨analyze_counter (generated := body) hb,
        scope_supported (ih hb ⟨hout.1, hout.2.1⟩ hout.2.2) hscope⟩
    | assign i rhs =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨value, hv, haction⟩ := hg
      apply (bind_supported (P := Below) (Q := Below) term_mono term_mono (ih hv he hp) ?_ haction).2
      intro out next output _ hout hupdate
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hupdate
      obtain ⟨updated, hu, heq⟩ := hupdate
      cases heq
      exact ⟨Nat.le_refl _, single_supported trivial (update_bounded hu hout.2.1 hout.1) hout.2.2⟩
    | ifE condition yes no =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨test, ht, hbranches⟩ := hg
      apply (bind_supported (P := Below) (Q := Below) term_mono term_mono (ih ht he hp) ?_ hbranches).2
      intro out next output _ hout haction
      simp only [Option.bind_eq_some_iff, Option.pure_def] at haction
      obtain ⟨a, ha, b, hb, heq⟩ := haction
      cases heq
      have na := analyze_counter ha
      have nb := analyze_counter hb
      have n := Nat.le_trans na nb
      have sa := ih ha hout.2.1 ⟨hout.2.2, hout.1⟩
      have sb := ih hb (symbols_below_mono hout.2.1 na)
        ⟨formula_bound_mono hout.2.2 na, below_mono hout.1 na⟩
      exact ⟨n, add_check_supported (combine_supported term_mono nb sa sb)
        (formula_bound_mono hout.2.2 n) (below_mono hout.1 n)⟩
    | unary op arg =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨argument, ha, haction⟩ := hg
      apply (bind_supported (P := Below) (Q := Below) term_mono term_mono (ih ha he hp) ?_ haction).2
      intro out next output _ hout heq
      cases heq
      exact ⟨Nat.le_refl _, add_check_supported
        (single_supported hout.1 hout.2.1 hout.2.2) hout.2.2 (unary_guard_bounded hout.1)⟩
    | binary op left right =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨lhs, hl, haction⟩ := hg
      apply (bind_supported (P := Below) (Q := Below) term_mono term_mono (ih hl he hp) ?_ haction).2
      intro a next output _ ha hrhs
      simp only [Option.bind_eq_some_iff] at hrhs
      obtain ⟨rhs, hr, executed, hx, hfinal⟩ := hrhs
      have nr := analyze_counter hr
      have hpath : FormulaBelow next
          (if shortable op then .and a.path (.not (shortGuard op a.value)) else a.path) := by
        split
        · exact ⟨ha.2.2, short_guard_bounded ha.1⟩
        · exact ha.2.2
      have sr := ih hr ha.2.1 hpath
      obtain ⟨nx, sx⟩ := bind_supported (P := Below) (Q := Below) term_mono term_mono sr
        (hg := hx) (by
          intro b current generated hnext hb heq
          cases heq
          have av := below_mono ha.1 (Nat.le_trans nr hnext)
          exact ⟨Nat.le_refl _, add_check_supported
            (single_supported ⟨av, hb.1⟩ hb.2.1 hb.2.2)
            hb.2.2 (binary_guard_bounded av hb.1)⟩)
      have n := Nat.le_trans nr nx
      split at hfinal
      next =>
        cases hfinal
        refine ⟨n, ?_, sx.2⟩
        intro out ho
        rcases List.mem_cons.mp ho with rfl | ho
        · exact ⟨below_mono ha.1 n, symbols_below_mono ha.2.1 n,
            formula_bound_mono ha.2.2 n, short_guard_bounded (below_mono ha.1 n)⟩
        · exact sx.1 out ho
      next => cases hfinal; exact ⟨n, sx⟩
    | call function args =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨actuals, ha, hcall⟩ := hg
      obtain ⟨_, sa⟩ := arguments_supported
        (fun _ _ _ _ _ he hp hg => ⟨analyze_counter hg, ih hg he hp⟩) he hp ha
      apply (bind_supported (P := SymbolsBelow) (Q := Below) symbols_mono term_mono sa ?_ hcall).2
      intro out next output _ hout haction
      simp only [Option.bind_eq_some_iff] at haction
      obtain ⟨fn, hf, hbody⟩ := haction
      split at hbody
      next =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at hbody
        obtain ⟨⟨defined, truth⟩, hpre, body, hb, heq⟩ := hbody
        cases heq
        have n := analyze_counter hb
        have hs := ih hb (symbols_reverse hout.1) hout.2.2
        have hr := requires_bounded hpre hout.1
        refine ⟨n, add_check_supported (map_outcomes_supported hs ?_)
          (formula_bound_mono hout.2.2 n)
          ⟨formula_bound_mono hr.1 n, formula_bound_mono hr.2 n⟩⟩
        intro result hresult
        exact ⟨hresult.1, symbols_below_mono hout.2.1 n, hresult.2.2⟩
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
        have si := (assertions_bounded hi he hp).1
        obtain ⟨nh, sh, dh⟩ := fresh_head_bounded hh he
        have hinvb := (assertions_bounded hinv sh (formula_bound_mono hp nh)).2
        have nc := analyze_counter hc
        have sc := ih hc sh ⟨formula_bound_mono hp nh, dh, hinvb⟩
        obtain ⟨nt, st⟩ := bind_supported (P := Below) (Q := Below) term_mono term_mono sc
          (hg := hit) (by
            intro out next output _ hout haction
            simp only [Option.bind_eq_some_iff] at haction
            obtain ⟨bodyResult, hb, preservation, hpres, heq⟩ := haction
            cases heq
            have nb := analyze_counter hb
            have sb := ih hb hout.2.1 ⟨hout.2.2, hout.1⟩
            obtain ⟨np, sp⟩ := bind_supported (P := Below) (Q := Below) term_mono term_mono sb
              (hg := hpres) (by
                intro final next generated _ hfinal hass
                simp only [Option.bind_eq_some_iff] at hass
                obtain ⟨⟨checks, truth⟩, hass, heq⟩ := hass
                cases heq
                exact ⟨Nat.le_refl _, (by intro out ho; cases ho),
                  (assertions_bounded hass hfinal.2.1 hfinal.2.2).1⟩)
            have n := Nat.le_trans nb np
            refine ⟨n, add_check_supported ?_ (formula_bound_mono hout.2.2 n) (below_mono hout.1 n)⟩
            refine ⟨?_, sp.2⟩
            intro result hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            subst result
            exact ⟨trivial, symbols_below_mono hout.2.1 n,
              formula_bound_mono hout.2.2 n, below_mono hout.1 n⟩)
        exact ⟨st.1, checks_append (checks_mono (Nat.le_trans nh (Nat.le_trans nc nt)) si) st.2⟩

theorem analyze_bounded
    (hg : analyze fs preconditions height Γ e env path start = some generated)
    (he : SymbolsBelow start env) (hp : FormulaBelow start path) :
    start ≤ generated.next ∧ Supported Below generated :=
  ⟨analyze_counter hg, analyze_supported hg he hp⟩

theorem group_bounded (hc : ChecksBelow n checks) : FormulaBelow n (group checks) := by
  induction checks with
  | nil => trivial
  | cons check rest ih =>
    exact ⟨hc check (by simp), ih (fun item hm => hc item (List.mem_cons_of_mem _ hm))⟩

/-- Every variable in an earlier artifact is strictly below each newly allocated
identity. This concerns recorded artifacts, not a missing allocation-event log. -/
theorem subsequent_head_separation (hs : Supported Below analysis)
    (hg : freshEnv Γ syms analysis.next = some (head, final))
    (hi : headIds Γ head = some ids) :
    ∀ identity ∈ ids,
      (∀ out ∈ analysis.outcomes, OutcomeBelow Below identity out) ∧
      ChecksBelow identity analysis.checks := by
  obtain ⟨actualIds, hids, _, hbounds⟩ := fresh_distinct hg
  rw [hi] at hids
  cases hids
  intro identity hid
  have lower := (hbounds identity hid).1
  exact ⟨fun out ho => outcome_mono term_mono lower (hs.1 out ho), checks_mono lower hs.2⟩

end APL.LoopVCG
