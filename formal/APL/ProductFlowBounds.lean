import APL.ProductFlow

namespace APL.ProductFlow
open ProductLogic
open ProductAnnotations (Instantiated)

def Analysis.Bounded (flow : Analysis SymValue) : Prop :=
  flow.value.Supported flow.next ∧ SymbolsBelow flow.next flow.env ∧ flow.normal.Supported flow.next

def Analysis.ArgsBounded (flow : Analysis (List SymValue)) : Prop :=
  SymbolsBelow flow.next flow.value ∧ SymbolsBelow flow.next flow.env ∧ flow.normal.Supported flow.next

theorem as_boolean_supported (hg : asBoolean value = some term) (h : value.Supported bound) :
    term.Supported bound := by
  cases value with
  | tuple fields => simp [asBoolean] at hg
  | scalar value =>
    simp only [asBoolean] at hg
    split at hg
    · cases hg; exact h
    · contradiction

theorem as_scalar_supported (hg : asScalar value = some scalar) (h : value.Supported bound) :
    scalar.Supported bound := by
  cases value with
  | tuple fields => simp [asScalar] at hg
  | scalar value => cases hg; exact h

theorem tuple_symbol_supported (hg : tupleSymbol values = some value) (h : SymbolsBelow bound values) :
    value.Supported bound := by
  simp only [tupleSymbol, bind, Option.bind_eq_some_iff] at hg
  obtain ⟨fields, hf, hg⟩ := hg
  exact construct_supported hg (ProductAnnotations.mapM_property hf
    (fun value hv field hg => as_scalar_supported hg (h value hv)))

theorem runtime_unary_supported (hg : runtimeUnary op value = some output) (h : value.Supported bound) :
    output.value.Supported bound := by
  cases value with
  | tuple fields => simp [runtimeUnary] at hg
  | scalar value =>
    simp only [runtimeUnary] at hg
    split at hg
    · cases hg; exact h
    · contradiction

theorem runtime_binary_supported (hg : runtimeBinary op left right = some output)
    (hl : left.Supported bound) (hr : right.Supported bound) : output.value.Supported bound := by
  cases left with
  | scalar left =>
    cases right with
    | scalar right =>
      simp only [runtimeBinary, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨type, _, heq⟩ := hg
      cases heq
      exact ⟨hl, hr⟩
    | tuple right => simp [runtimeBinary, SymValue.type, FlatProducts.binaryType] at hg
  | tuple left =>
    cases right with
    | scalar right => simp [runtimeBinary, SymValue.type, FlatProducts.binaryType] at hg
    | tuple right =>
      simp only [runtimeBinary, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨type, _, term, ht, heq⟩ := hg
      cases heq
      split at ht
      · exact inequality_supported ht hl hr
      · exact equality_supported ht hl hr

theorem update_symbols_supported (hg : updateSymbols symbols index value = some output)
    (hs : SymbolsBelow bound symbols) (hv : value.Supported bound) : SymbolsBelow bound output := by
  induction symbols generalizing index output with
  | nil => simp [updateSymbols] at hg
  | cons symbol symbols ih =>
    cases index with
    | zero =>
      cases hg
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact hv
      · exact hs value (by simp [member])
    | succ index =>
      simp only [updateSymbols, Option.map_eq_some_iff] at hg
      obtain ⟨rest, hr, rfl⟩ := hg
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact hs _ (by simp)
      · exact ih hr (fun value hv => hs value (by simp [hv])) value member

theorem symbols_tail (h : SymbolsBelow bound symbols) : SymbolsBelow bound symbols.tail := by
  cases symbols with
  | nil => intro value hv; cases hv
  | cons symbol symbols => intro value hv; exact h value (List.mem_cons_of_mem symbol hv)

theorem symbols_reverse (h : SymbolsBelow bound symbols) : SymbolsBelow bound symbols.reverse := by
  intro value hv
  exact h value (List.mem_reverse.mp hv)

theorem fresh_head_bounded (hg : freshHead context symbols start = some head)
    (h : SymbolsBelow start symbols) : start ≤ head.next ∧ SymbolsBelow head.next head.symbols ∧
      head.domain.Supported head.next := by
  simp only [freshHead, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨⟨values, finish⟩, hf, heq⟩ := hg
  cases heq
  obtain ⟨hn, hb⟩ := fresh_env_bounded hf h
  exact ⟨hn, hb, env_domain_supported hb⟩

theorem merge_flow_bounded (hg : mergeFlow condition yes no = some output)
    (hc : condition.Supported no.next) (hy : yes.Bounded) (hn : no.Bounded)
    (hnext : yes.next ≤ no.next) : output.Bounded := by
  simp only [mergeFlow, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
  obtain ⟨value, hv, env, he, heq⟩ := hg
  cases heq
  exact ⟨merge_supported hv hc (value_supported_mono hy.1 hnext) hn.1,
    merge_env_supported he hc (symbols_supported_mono hy.2.1 hnext) hn.2.1,
    formula_supported_mono hy.2.2 hnext, hn.2.2⟩

theorem arguments_bounded
    (ha : ∀ term env path start site output, generate term env path start site = some output →
      SymbolsBelow start env → path.Supported start → start ≤ output.next ∧ output.Bounded)
    (hg : arguments generate terms env path start site index = some output)
    (he : SymbolsBelow start env) (hp : path.Supported start) :
    start ≤ output.next ∧ output.ArgsBounded := by
  induction terms generalizing env path start index output with
  | nil =>
    cases hg
    refine ⟨Nat.le_refl _, ?_, he, hp⟩
    intro value hv
    cases hv
  | cons term terms ih =>
    simp only [arguments, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, hf, rest, hr, heq⟩ := hg
    cases heq
    obtain ⟨hfirst, hb⟩ := ha term env path start _ first hf he hp
    obtain ⟨hrest, hrb⟩ := ih hr hb.2.1 hb.2.2
    refine ⟨Nat.le_trans hfirst hrest, ?_, hrb.2⟩
    intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact value_supported_mono hb.1 hrest
    · exact hrb.1 value hv

theorem analyze_bounded (hg : analyze fs height context term env path start site = some output)
    (he : SymbolsBelow start env) (hp : path.Supported start) :
    start ≤ output.next ∧ output.Bounded := by
  induction height generalizing context term env path start site output with
  | zero => simp [analyze] at hg
  | succ height ih =>
    simp only [analyze, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨type, _, hg⟩ := hg
    cases term with
    | lit value => cases hg; exact ⟨Nat.le_refl _, runtime_literal_supported, he, hp⟩
    | «local» index =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨value, hv, heq⟩ := hg
      cases heq
      exact ⟨Nat.le_refl _, supported_lookup he hv, he, hp⟩
    | letE value body | letMut value body =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨type, _, first, hf, body, hb, _, _, heq⟩ := hg
      cases heq
      obtain ⟨hn, hfirst⟩ := ih hf he hp
      have henv : SymbolsBelow first.next (first.value :: first.env) := by
        intro value hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hfirst.1
        · exact hfirst.2.1 value hv
      obtain ⟨hn', hbody⟩ := ih hb henv hfirst.2.2
      exact ⟨Nat.le_trans hn hn', hbody.1, symbols_tail hbody.2.1, hbody.2.2⟩
    | assign index value =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨first, hf, final, hu, heq⟩ := hg
      cases heq
      obtain ⟨hn, hb⟩ := ih hf he hp
      exact ⟨hn, runtime_literal_supported (value := .scalar .unit), update_symbols_supported hu hb.2.1 hb.1, hb.2.2⟩
    | ifE condition yes no =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨test, ht, condition, hc, yes, hy, no, hn, merged, hm, heq⟩ := hg
      cases heq
      obtain ⟨nt, bt⟩ := ih ht he hp
      have cb := as_boolean_supported hc bt.1
      obtain ⟨ny, byes⟩ := ih hy bt.2.1 ⟨bt.2.2, cb⟩
      obtain ⟨nn, bno⟩ := ih hn (symbols_supported_mono bt.2.1 ny)
        ⟨formula_supported_mono bt.2.2 ny, condition.supported_mono cb ny⟩
      have hm' := merge_flow_bounded hm (condition.supported_mono cb (Nat.le_trans ny nn)) byes bno nn
      have mergedNext : merged.next = no.next := by
        simp only [mergeFlow, bind, Option.bind_eq_some_iff, Option.pure_def] at hm
        obtain ⟨_, _, _, _, heq⟩ := hm
        cases heq; rfl
      exact ⟨mergedNext ▸ Nat.le_trans nt (Nat.le_trans ny nn), hm'⟩
    | unary op arg =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨first, hf, value, hv, heq⟩ := hg
      cases heq
      obtain ⟨hn, hb⟩ := ih hf he hp
      exact ⟨hn, runtime_unary_supported hv hb.1, hb.2⟩
    | binary op left right =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨left, hl, hg⟩ := hg
      obtain ⟨nl, bl⟩ := ih hl he hp
      split at hg
      next hshort =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
        obtain ⟨condition, hc, right, hr, merged, hm, heq⟩ := hg
        cases heq
        have cb := as_boolean_supported hc bl.1
        have pathBound : (if op = .and then Formula.holds condition else .holds (.unary .not condition)).Supported left.next := by
          split <;> exact cb
        obtain ⟨nr, br⟩ := ih hr bl.2.1 ⟨bl.2.2, pathBound⟩
        have skippedBound : (single left.value left.env
            (.and left.normal (if op = .and then Formula.holds (.unary .not condition) else .holds condition)) right.next).Bounded := by
          refine ⟨value_supported_mono bl.1 nr, symbols_supported_mono bl.2.1 nr,
            formula_supported_mono bl.2.2 nr, ?_⟩
          split <;> exact condition.supported_mono cb nr
        have mergedBound : merged.Bounded := by
          split at hm
          next hand =>
            exact merge_flow_bounded hm (condition.supported_mono cb nr) br
              (by simpa only [hand, ↓reduceIte] using skippedBound) (Nat.le_refl _)
          next hand =>
            exact merge_flow_bounded hm (condition.supported_mono cb nr)
              (by simpa only [hand, ↓reduceIte] using skippedBound) br (Nat.le_refl _)
        have mergedNext : merged.next = right.next := by
          split at hm <;>
            simp only [mergeFlow, bind, Option.bind_eq_some_iff, Option.pure_def] at hm
          all_goals obtain ⟨_, _, _, _, heq⟩ := hm; cases heq; rfl
        exact ⟨mergedNext ▸ Nat.le_trans nl nr, mergedBound⟩
      next hstrict =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
        obtain ⟨right, hr, value, hv, heq⟩ := hg
        cases heq
        obtain ⟨nr, br⟩ := ih hr bl.2.1 bl.2.2
        exact ⟨Nat.le_trans nl nr,
          runtime_binary_supported hv (value_supported_mono bl.1 nr) br.1, br.2⟩
    | call function args =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨actuals, ha, fn, hf, hg⟩ := hg
      split at hg
      next ht =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
        obtain ⟨_, _, body, hb, heq⟩ := hg
        cases heq
        obtain ⟨na, ba⟩ := arguments_bounded (fun _ _ _ _ _ _ => ih) ha he hp
        obtain ⟨nb, bb⟩ := ih hb (symbols_reverse ba.1) ba.2.2
        exact ⟨Nat.le_trans na nb, bb.1, symbols_supported_mono ba.2.1 nb, bb.2.2⟩
      · contradiction
    | tuple fields =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨captured, hc, value, hv, heq⟩ := hg
      cases heq
      obtain ⟨hn, hb⟩ := arguments_bounded (fun _ _ _ _ _ _ => ih) hc he hp
      exact ⟨hn, tuple_symbol_supported hv hb.1, hb.2⟩
    | project base index =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨base, hb, field, hf, heq⟩ := hg
      cases heq
      obtain ⟨hn, hb⟩ := ih hb he hp
      exact ⟨hn, project_supported hf hb.1, hb.2⟩
    | whileE clauses condition body =>
      dsimp only at hg
      split at hg
      · contradiction
      next hnonempty =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
        obtain ⟨initial, _, head, hh, invariant, hi, condition, hc, test, ht, body, hb,
          preservation, _, heq⟩ := hg
        cases heq
        obtain ⟨nh, hhead, hdomain⟩ := fresh_head_bounded hh he
        have hinv := ProductAnnotations.clause_conjunction_supported
          (ProductAnnotations.assertions_supported hi (by intro value hv; cases hv)
            (by intro value hv; cases hv) hhead)
        obtain ⟨nc, bc⟩ := ih hc hhead ⟨formula_supported_mono hp nh, hdomain, hinv⟩
        have htest := as_boolean_supported ht bc.1
        obtain ⟨nb, bb⟩ := ih hb bc.2.1 ⟨bc.2.2, htest⟩
        exact ⟨Nat.le_trans nh (Nat.le_trans nc nb), runtime_literal_supported (value := .scalar .unit),
          symbols_supported_mono bc.2.1 nb, formula_supported_mono bc.2.2 nb,
          test.supported_mono htest nb⟩

end APL.ProductFlow
