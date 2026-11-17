import APL.ProductFlowCalls

namespace APL.ProductFlow
open ProductLogic
open ProductAnnotations (eraseFunctions)
open FlatProducts.LoopVerification

theorem logical_types (hl : op = .and ∨ op = .or)
    (ht : FlatProducts.binaryType op a b = some type) : a = .scalar .bool ∧ b = .scalar .bool := by
  rcases hl with rfl | rfl
  all_goals
    cases a with
    | tuple _ => cases b <;> simp [FlatProducts.binaryType] at ht
    | scalar a =>
      cases b with
      | tuple _ => simp [FlatProducts.binaryType] at ht
      | scalar b => cases a <;> cases b <;> simp_all [FlatProducts.binaryType, APL.binaryType]

theorem symbols_cons (hv : value.Supported bound) (he : SymbolsBelow bound symbols) :
    SymbolsBelow bound (value :: symbols) := by
  intro other ho
  rcases List.mem_cons.mp ho with rfl | ho
  · exact hv
  · exact he other ho

theorem analyze_sound
    (wf : FlatProducts.WellTyped (eraseFunctions fs))
    (hg : analyze fs height context term symbols path start site = some output)
    (he : SymbolsBelow start symbols) (hp : path.Supported start) :
    SoundAt (eraseFunctions fs) term.erase context symbols path start output := by
  induction height generalizing context term symbols path start site output with
  | zero => simp [analyze] at hg
  | succ height ih =>
    simp only [analyze, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨type, inferred, hg⟩ := hg
    have typed : FlatProducts.HasType (FlatProducts.signatures (eraseFunctions fs)) context term.erase type := by
      rw [ProductAnnotations.erase_signatures]
      exact FlatProducts.infer_sound inferred
    cases term with
    | lit value =>
      cases hg
      simp only [ProductAnnotations.Term.erase]
      exact literal_sound
    | «local» index =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨value, hv, heq⟩ := hg
      cases heq
      simp only [ProductAnnotations.Term.erase]
      exact local_sound hv
    | letE value body | letMut value body =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨type, htype, first, hf, bodyResult, hb, cell, hcell, heq⟩ := hg
      cases heq
      have initialTyped : FlatProducts.HasType (FlatProducts.signatures (eraseFunctions fs)) context value.erase type := by
        rw [ProductAnnotations.erase_signatures]
        exact FlatProducts.infer_sound htype
      obtain ⟨hn, bfirst⟩ := analyze_bounded hf he hp
      have bodySound := ih hb (symbols_cons bfirst.1 bfirst.2.1) bfirst.2.2
      simp only [ProductAnnotations.Term.erase]
      exact binding_analysis_sound wf initialTyped (ih hf he hp) hn bodySound hcell
    | assign index value =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨first, hf, final, hu, heq⟩ := hg
      cases heq
      simp only [ProductAnnotations.Term.erase]
      exact assignment_analysis_sound (ih hf he hp) hu
    | unary op arg =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨first, hf, value, hv, heq⟩ := hg
      cases heq
      simp only [ProductAnnotations.Term.erase]
      exact unary_analysis_sound (ih hf he hp) hv
    | project base index =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨first, hf, field, hfield, heq⟩ := hg
      cases heq
      simp only [ProductAnnotations.Term.erase]
      exact projection_analysis_sound (ih hf he hp) hfield
    | ifE condition yes no =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨first, hf, test, ht, yesResult, hy, noResult, hn, merged, hm, heq⟩ := hg
      cases heq
      obtain ⟨nf, bf⟩ := analyze_bounded hf he hp
      have cb := as_boolean_supported ht bf.1
      obtain ⟨ny, _⟩ := analyze_bounded hy bf.2.1 ⟨bf.2.2, cb⟩
      have yesSound := ih hy bf.2.1 ⟨bf.2.2, cb⟩
      have noSound := ih hn (symbols_supported_mono bf.2.1 ny)
        ⟨formula_supported_mono bf.2.2 ny, test.supported_mono cb ny⟩
      simp only [ProductAnnotations.Term.erase] at typed ⊢
      cases typed with
      | ifE htc _ _ => exact conditional_analysis_sound wf htc (ih hf he hp) nf bf ht yesSound ny noSound hm
    | binary op left right =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨first, hf, hg⟩ := hg
      obtain ⟨nf, bf⟩ := analyze_bounded hf he hp
      simp only [ProductAnnotations.Term.erase] at typed ⊢
      cases typed with
      | binary htl htr htop =>
        split at hg
        next hlogical =>
          simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
          obtain ⟨test, ht, second, hs, merged, hm, heq⟩ := hg
          cases heq
          obtain ⟨rfl, rfl⟩ := logical_types hlogical htop
          have testBound := as_boolean_supported ht bf.1
          have pathBound : (if op = .and then Formula.holds test else .holds (.unary .not test)).Supported first.next := by
            split <;> exact testBound
          have rightSound := ih hs bf.2.1 ⟨bf.2.2, pathBound⟩
          rcases hlogical with rfl | rfl
          · apply logical_binary_analysis_sound (isAnd := true) wf htl htr (ih hf he hp) nf bf ht
            · simpa only [↓reduceIte] using rightSound
            · simpa only [↓reduceIte] using hm
          · apply logical_binary_analysis_sound (isAnd := false) wf htl htr (ih hf he hp) nf bf ht
            · simpa using rightSound
            · simpa using hm
        next hstrict =>
          simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
          obtain ⟨second, hs, result, hr, heq⟩ := hg
          cases heq
          exact strict_binary_analysis_sound wf htl (ih hf he hp) nf bf (ih hs bf.2.1 bf.2.2) hr hstrict
    | call function args =>
      simp only [Option.bind_eq_some_iff] at hg
      obtain ⟨actuals, ha, fn, hf, hg⟩ := hg
      split at hg
      next ht =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
        obtain ⟨required, _, bodyResult, hb, heq⟩ := hg
        cases heq
        obtain ⟨na, ba⟩ := arguments_bounded (fun _ _ _ _ _ _ => analyze_bounded) ha he hp
        have bodySound := ih hb (symbols_reverse ba.1) ba.2.2
        simp only [ProductAnnotations.Term.erase] at typed ⊢
        cases typed with
        | call _ hat =>
          apply call_analysis_sound (an := na) (ab := ba) (hf := hf) (ht := ht) (bs := bodySound)
          intro model env henv htyped hpath valid
          exact arguments_sound wf (fun _ _ _ _ _ _ => analyze_bounded)
            (fun _ _ _ _ _ _ => ih) ha hat he hp henv htyped hpath valid
      · contradiction
    | tuple fields =>
      simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨captured, hc, value, hv, heq⟩ := hg
      cases heq
      simp only [ProductAnnotations.Term.erase] at typed ⊢
      cases typed with
      | tuple hat =>
        apply tuple_analysis_sound wf hat (hg := hv)
        intro model env henv htyped hpath valid
        exact arguments_sound wf (fun _ _ _ _ _ _ => analyze_bounded)
          (fun _ _ _ _ _ _ => ih) hc hat he hp henv htyped hpath valid
    | whileE clauses condition body =>
      dsimp only at hg
      split at hg
      · contradiction
      next _ =>
        simp only [Option.bind_eq_some_iff, Option.pure_def] at hg
        obtain ⟨initial, hi, head, hh, invariant, hinv, conditionResult, hc, test, ht,
          bodyResult, hb, preservedClauses, hpres, heq⟩ := hg
        cases heq
        obtain ⟨nh, hhead, hdomain⟩ := fresh_head_bounded hh he
        have invariantBound := ProductAnnotations.clause_conjunction_supported
          (ProductAnnotations.assertions_supported hinv (by intro value hv; cases hv)
            (by intro value hv; cases hv) hhead)
        have headPathBound := And.intro (formula_supported_mono hp nh) (And.intro hdomain invariantBound)
        obtain ⟨nc, bc⟩ := analyze_bounded hc hhead headPathBound
        have conditionSound := ih hc hhead headPathBound
        have bodySound := ih hb bc.2.1 ⟨bc.2.2, as_boolean_supported ht bc.1⟩
        simp only [ProductAnnotations.Term.erase] at typed ⊢
        cases typed with
        | whileE htc htb =>
          exact loop_analysis_sound wf htc htb he hp hi hh hinv conditionSound nc ht bodySound hpres

theorem analyze_run_sound
    (wf : FlatProducts.WellTyped (eraseFunctions fs))
    (hg : analyze fs height context term symbols path start site = some output)
    (he : SymbolsBelow start symbols) (hp : path.Supported start)
    (hr : RuntimeEnvRep model symbols env) (ht : FlatProducts.EnvTyped env context)
    (hpath : path.Holds model) (valid : ValidFrom start model output.checks) :
    RunSafe (Covered start model output)
      (FlatProducts.run (eraseFunctions fs) budget (.eval term.erase env [])) :=
  closed_run (analyze_sound wf hg he hp model env hr ht hpath valid)

theorem analyze_no_finite_trap
    (wf : FlatProducts.WellTyped (eraseFunctions fs))
    (hg : analyze fs height context term symbols path start site = some output)
    (he : SymbolsBelow start symbols) (hp : path.Supported start)
    (hr : RuntimeEnvRep model symbols env) (ht : FlatProducts.EnvTyped env context)
    (hpath : path.Holds model) (valid : ValidFrom start model output.checks) :
    ¬ FlatProducts.Steps (eraseFunctions fs) (.eval term.erase env []) (.trap kind) :=
  no_finite_trap (analyze_sound wf hg he hp model env hr ht hpath valid)

theorem analyze_no_finite_invalid
    (wf : FlatProducts.WellTyped (eraseFunctions fs))
    (hg : analyze fs height context term symbols path start site = some output)
    (he : SymbolsBelow start symbols) (hp : path.Supported start)
    (hr : RuntimeEnvRep model symbols env) (ht : FlatProducts.EnvTyped env context)
    (hpath : path.Holds model) (valid : ValidFrom start model output.checks) :
    ¬ FlatProducts.Steps (eraseFunctions fs) (.eval term.erase env []) .invalid :=
  no_finite_invalid (analyze_sound wf hg he hp model env hr ht hpath valid)

theorem analyze_normal_coverage
    (wf : FlatProducts.WellTyped (eraseFunctions fs))
    (hg : analyze fs height context term symbols path start site = some output)
    (he : SymbolsBelow start symbols) (hp : path.Supported start)
    (hr : RuntimeEnvRep model symbols env) (ht : FlatProducts.EnvTyped env context)
    (hpath : path.Holds model) (valid : ValidFrom start model output.checks)
    (trace : FlatProducts.Steps (eraseFunctions fs) (.eval term.erase env []) (.ret value final [])) :
    Covered start model output value final :=
  normal_result (analyze_sound wf hg he hp model env hr ht hpath valid) trace

end APL.ProductFlow
