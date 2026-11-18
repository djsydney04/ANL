import ANL.WordsRunProofs
import ANL.WordsLayout

namespace ANL.Words

open ANL.Memory


theorem typed_eval (he : HasType p.signatures Γ (resourceModes a.resources) e u)
    (hen : EnvTyped a.env Γ) (hk : KontTyped p.signatures Γ a.resources a.function k u t)
    (hl : Layout (w.owners.map Owner.shape) a.resources k) (hw : w.Valid p.profile) :
    State.Typed p ⟨.eval e, a, k, w⟩ t := .intro hen (.eval he) hk hl hw

theorem typed_ret (hen : EnvTyped a.env Γ)
    (hk : KontTyped p.signatures Γ a.resources a.function k v.type t)
    (hl : Layout (w.owners.map Owner.shape) a.resources k) (hw : w.Valid p.profile) :
    State.Typed p ⟨.ret v, a, k, w⟩ t := .intro hen .ret hk hl hw

theorem typed_resume (hr : Result.Typed u result) (hen : EnvTyped a.env Γ)
    (hk : KontTyped p.signatures Γ a.resources a.function k u t)
    (hl : Layout (w.owners.map Owner.shape) a.resources k) (hw : w.Valid p.profile) :
    State.Typed p (resume result a k w) t := by
  cases result with
  | value value => exact typed_ret hen (by simpa [Result.Typed] using hr ▸ hk) hl hw
  | trap kind => exact .intro hen .trap hk hl hw
  | invalid => exact False.elim hr

theorem args_scalar_cons {types : List ScalarTy}
    (h : ArgsTyped sigs Γ R (e :: es) (types.map Ty.scalar)) :
    ∃ a rest, types = a :: rest ∧ HasType sigs Γ R e (.scalar a) ∧
      ArgsTyped sigs Γ R es (rest.map Ty.scalar) := by
  cases types with
  | nil => cases h
  | cons a rest => cases h with
    | cons ha hs => exact ⟨a, rest, rfl, ha, hs⟩

theorem args_scalar_nil {types : List ScalarTy}
    (h : ArgsTyped sigs Γ R [] (types.map Ty.scalar)) : types = [] := by
  cases types with | nil => rfl | cons a rest => cases h

theorem beginArguments_typed
    (ha : ArgsTyped p.signatures Γ (resourceModes a.resources) args types)
    (hf : p.signatures[f]? = some fn) (hm : fn.view = loanMode loan)
    (hp : fn.params = (values.map Val.type).reverse ++ types)
    (hv : LoanOption.Valid loan a.resources) (hen : EnvTyped a.env Γ)
    (hk : KontTyped p.signatures Γ a.resources a.function k fn.result t)
    (hl : Layout (w.owners.map Owner.shape) a.resources k) (hw : w.Valid p.profile) :
    State.Typed p (beginArguments f loan args values a k w) t := by
  cases ha with
  | nil => exact .intro hen (.invoke hf hm (by simpa using hp) hv) hk hl hw
  | cons he rest => exact typed_eval he hen (.cons (.arguments rest hf hm hp hv) hk) (.plain trivial hl) hw

theorem preservation (wf : WellFormedProgram p) (h : State.Typed p s t)
    (hs : Step p responses s next) : State.Typed p next t := by
  cases hs with
  | lit =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he; exact typed_ret hen hk hl hw
  | word =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | word hs => exact typed_resume (wordLiteral_typed hs) hen hk hl hw
  | convertEval =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | convert he hs => exact typed_eval he hen (.cons (.convert hs) hk) (.plain trivial hl) hw
  | localFound hv =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | «local» hi =>
        obtain ⟨v, hv', ht⟩ := env_lookup hen hi
        rw [hv] at hv'; cases hv'
        exact typed_ret hen (ht ▸ hk) hl hw
  | localMissing hv =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | «local» hi =>
        obtain ⟨v, hv', _⟩ := env_lookup hen hi
        rw [hv] at hv'; contradiction
  | letEval =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | letE ha hb =>
        exact typed_eval ha hen (.cons (.bind hb) hk) (.plain trivial hl) hw
  | letMutEval =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | letMut ha hb =>
        exact typed_eval ha hen (.cons (.bind hb) hk) (.plain trivial hl) hw
  | assignEval =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | assign hi ha =>
        exact typed_eval ha hen (.cons (.assign hi) hk) (.plain trivial hl) hw
  | whileEval =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | whileE hc hb =>
        exact typed_eval hc hen (.cons (.condition hc hb) hk) (.plain trivial hl) hw
  | ifEval =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | ifE hc hy hn =>
        exact typed_eval hc hen (.cons (.ifF hy hn) hk) (.plain trivial hl) hw
  | unaryEval =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | unary he hop =>
        exact typed_eval he hen (.cons (.unary hop) hk) (.plain trivial hl) hw
  | binaryEval =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | binary ha hb hop =>
        exact typed_eval ha hen (.cons (.left hb hop) hk) (.plain trivial hl) hw
  | call =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | call hf hm ha =>
        exact beginArguments_typed ha hf hm rfl trivial hen hk hl hw
  | tupleEmpty =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      have hi := checkTerm_complete he
      simp [checkTerm, annotated, APL.FlatProducts.Flat.make] at hi
  | tupleFirst =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | tuple ha =>
        obtain ⟨a, rest, hs, ha, hr⟩ := args_scalar_cons ha
        exact typed_eval ha hen (.cons (.fields hr (by simpa using hs.symm)) hk) (.plain trivial hl) hw
  | projectEval =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | project he hi =>
        exact typed_eval he hen (.cons (.project hi) hk) (.plain trivial hl) hw
  | heapEval =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | heap hlen hinit hy hn =>
        exact typed_eval hlen hen (.cons (.heapLength rfl hinit hy hn) hk) (.plain trivial hl) hw
  | lengthFound hi =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | bufferLength ht =>
        exact typed_resume (legacyResult_typed (APL.checked_typed _)) hen hk hl hw
  | lengthMissing hi =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | bufferLength ht =>
        obtain ⟨b, hb, _⟩ := resource_lookup ht
        rw [hi] at hb; contradiction
  | readEval hi =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | bufferRead ht hx =>
        exact typed_eval hx hen (.cons (.readIndex (List.mem_of_getElem? hi)) hk) (.plain trivial hl) hw
  | readMissing hi =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | bufferRead ht _ =>
        obtain ⟨b, hb, _⟩ := resource_lookup ht
        rw [hi] at hb; contradiction
  | writeEval hi hp =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | bufferWrite ht hm hx hv =>
        exact typed_eval hx hen (.cons (.writeIndex (List.mem_of_getElem? hi) hp hv) hk) (.plain trivial hl) hw
  | writeMissing hi =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | bufferWrite ht _ _ _ =>
        obtain ⟨b, hb, _⟩ := resource_lookup ht
        rw [hi] at hb; contradiction
  | writeDenied hi hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | bufferWrite ht hm _ _ =>
        obtain ⟨b, hb, he⟩ := resource_lookup ht
        rw [hi] at hb; cases hb
        exact False.elim (hn (he ▸ hm))
  | callView hi hp =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | callView hf hm ht _ ha =>
        exact beginArguments_typed ha hf hm rfl ⟨List.mem_of_getElem? hi, hp⟩ hen hk hl hw
  | viewMissing hi =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | callView _ _ ht _ _ =>
        obtain ⟨b, hb, _⟩ := resource_lookup ht
        rw [hi] at hb; contradiction
  | viewDenied hi hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | eval he =>
      cases he with
      | callView _ _ ht hm _ =>
        obtain ⟨b, hb, he⟩ := resource_lookup ht
        rw [hi] at hb; cases hb
        exact False.elim (hn (he ▸ hm))
  | bindReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | bind hb =>
        exact typed_eval hb (env_cons hen) (.cons .scope hk) (.plain trivial (hl.pop_plain trivial)) hw
  | scopeReturn he =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf
      rw [he] at hen
      exact typed_ret (env_tail hen) hk (hl.pop_plain trivial) hw
  | scopeMissing he =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf
      simp [EnvTyped, he] at hen
  | assignReturn hu =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | assign hi =>
        obtain ⟨env, hu', ht⟩ := update_typed hen hi
        rw [hu] at hu'; cases hu'
        exact typed_ret ht hk (hl.pop_plain trivial) hw
  | assignMissing hu =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | assign hi =>
        obtain ⟨env, hu', _⟩ := update_typed hen hi
        rw [hu] at hu'; contradiction
  | ifTrue =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | ifF hy _ =>
        exact typed_eval hy hen hk (hl.pop_plain trivial) hw
  | ifFalse =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | ifF _ hn =>
        exact typed_eval hn hen hk (hl.pop_plain trivial) hw
  | ifWrong hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    generalize hvtype : Val.type _ = input at hk
    cases hk with
    | cons hf hk =>
      cases hf; exact False.elim (hn hvtype)
  | convertReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | convert hop => exact typed_resume (convert_typed hop) hen hk (hl.pop_plain trivial) hw
  | unaryReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | unary hop => exact typed_resume (unary_typed hop) hen hk (hl.pop_plain trivial) hw
  | short hs =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | left hb hop =>
        exact typed_ret hen ((shortCircuit_typed hop hs) ▸ hk) (hl.pop_plain trivial) hw
  | rightEval =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | left hb hop =>
        exact typed_eval hb hen (.cons (.right hop) hk) (.plain trivial (hl.pop_plain trivial)) hw
  | binaryReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | right hop =>
        exact typed_resume (binary_typed hop) hen hk (hl.pop_plain trivial) hw
  | argumentReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | arguments ha hf hm hp hv =>
        apply beginArguments_typed ha hf hm (by simpa [List.reverse_cons, List.append_assoc] using hp) hv hen hk
        · exact hl.pop_plain trivial
        · exact hw
  | callResult =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    exact .intro hen (.revoke rfl) hk hl hw
  | whileTrue =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | condition hc hb =>
        exact typed_eval hb hen (.cons (.body hc hb) hk) (.plain trivial (hl.pop_plain trivial)) hw
  | whileFalse =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | condition hc hb =>
        exact typed_ret hen hk (hl.pop_plain trivial) hw
  | whileWrong hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    generalize hvtype : Val.type _ = input at hk
    cases hk with
    | cons hf hk =>
      cases hf; exact False.elim (hn hvtype)
  | whileAgain =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | body hc hb =>
        exact typed_eval hc hen (.cons (.condition hc hb) hk) (.plain trivial (hl.pop_plain trivial)) hw
  | bodyWrong hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    generalize hvtype : Val.type _ = input at hk
    cases hk with
    | cons hf hk =>
      cases hf; exact False.elim (hn hvtype)
  | fieldNext =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | fields ha hs =>
        obtain ⟨a, rest, hr, ha, ht⟩ := args_scalar_cons ha
        exact typed_eval ha hen (.cons (.fields ht (by
          simpa [List.reverse_cons, List.append_assoc, hr] using hs)) hk) (.plain trivial (hl.pop_plain trivial)) hw
  | fieldsDone =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | fields ha hs =>
        have hr := args_scalar_nil ha
        exact typed_resume (construct_typed (by
          simpa [List.map_reverse, List.reverse_cons, hr] using hs)) hen hk (hl.pop_plain trivial) hw
  | fieldTuple =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf
  | projectReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    generalize hv : Val.type _ = a at hk
    cases hk with | cons hf hk => cases hf with | project hi =>
      exact typed_resume (project_typed hv hi) hen hk (hl.pop_plain trivial) hw
  | heapLengthReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    generalize hvtype : Val.type _ = input at hk
    cases hk with
    | cons hf hk =>
      cases hf with
      | heapLength hf hi hy hn =>
        exact .intro hen (.lengthReady hf hvtype hi hy hn) hk (hl.pop_plain trivial) hw
  | heapInitialReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | heapInitial hf hy hn =>
        exact .intro hen (.allocate hf hy hn) hk (hl.pop_plain trivial) hw
  | heapInitialWrong hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    generalize hvtype : Val.type _ = input at hk
    cases hk with
    | cons hf hk =>
      cases hf; exact False.elim (hn hvtype)
  | ownerReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    exact .intro hen (.close rfl) hk hl hw
  | readIndexReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    generalize hvtype : Val.type _ = input at hk
    cases hk with
    | cons hf hk =>
      cases hf with
      | readIndex hm =>
        exact .intro hen (.readCheck hm hvtype) hk (hl.pop_plain trivial) hw
  | writeIndexReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    generalize hvtype : Val.type _ = input at hk
    cases hk with
    | cons hf hk =>
      cases hf with
      | writeIndex hm hp hv =>
        exact .intro hen (.writeCheck hm hp hvtype hv) hk (hl.pop_plain trivial) hw
  | writeValueReturn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    cases hk with
    | cons hf hk =>
      cases hf with
      | writeValue hm hp hi =>
        exact .intro hen (.store hm hp hi) hk (hl.pop_plain trivial) hw
  | writeValueWrong hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc
    generalize hvtype : Val.type _ = input at hk
    cases hk with
    | cons hf hk =>
      cases hf; exact False.elim (hn hvtype)
  | negativeLength =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | lengthReady =>
      exact .intro hen .trap hk hl hw
  | nonnegativeLength hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | lengthReady hf ht hi hy hn =>
      exact typed_eval hi hen (.cons (.heapInitial hf hy hn) hk) (.plain trivial hl) hw
  | lengthWrong hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | lengthReady hf ht hi hy hb =>
      exact False.elim (hn ht)
  | allocated ha =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | allocate hf hy hn =>
      apply typed_eval
      · exact hy
      · exact hen
      · exact .cons (.owner rfl hf) hk
      · rw [allocate_shapes ha]; exact .owner (binding := ⟨.owner, _, _⟩) rfl hl
      · exact allocate_eq_valid hw ha
  | allocationRefused ha =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | allocate hf hy hn =>
      apply typed_eval hn hen hk
      · simpa [allocate_failure_owners ha (.inl rfl)] using hl
      · exact allocate_eq_valid hw ha
  | allocationRejected ha =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | allocate hf hy hn =>
      apply typed_eval hn hen hk
      · simpa [allocate_failure_owners ha (.inr rfl)] using hl
      · exact allocate_eq_valid hw ha
  | readChecked hi =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | readCheck hm ht =>
      exact .intro hen (.readCell hm (checkedIndex_bounds hi).1) hk hl hw
  | readBounds =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | readCheck =>
      exact .intro hen .trap hk hl hw
  | readWrong hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | readCheck hm ht =>
      exact False.elim (hn ht)
  | readValue hv =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | readCell hm hi =>
      exact typed_ret hen hk hl hw
  | readUnavailable hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | readCell hm hi =>
      obtain ⟨owner, ho, he⟩ := hl.lookup hw hm
      obtain ⟨value, hv⟩ := World.read_exists ho (by simpa [he] using hi)
      rw [hn] at hv; contradiction
  | writeChecked hi =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | writeCheck hm hp ht hv =>
      exact typed_eval hv hen (.cons (.writeValue hm hp (checkedIndex_bounds hi).1) hk) (.plain trivial hl) hw
  | writeBounds =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | writeCheck =>
      exact .intro hen .trap hk hl hw
  | writeWrong hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | writeCheck hm hp ht hv =>
      exact False.elim (hn ht)
  | stored hs =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | store hm hp hi =>
      exact typed_ret hen hk (by rw [(World.write_footprint hs).1]; exact hl) (World.write_valid hw hs)
  | storeUnavailable hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | store hm hp hi =>
      obtain ⟨owner, ho, he⟩ := hl.lookup hw hm
      obtain ⟨next, hs⟩ := World.write_exists (value := _) ho (by simpa [he] using hi)
      rw [hn] at hs; contradiction
  | invoke hf hm =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | invoke hs hv hp hlv =>
      exact .intro hen (.grant hs hv hp hlv) hk hl hw
  | invokeMissing hf =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | invoke hs hv hp hlv =>
      obtain ⟨fn, hf', _⟩ := signatures_lookup_inv hs
      rw [hf] at hf'; contradiction
  | invokeMode hf hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | invoke hs hv hp hlv =>
      rw [signatures_lookup hf] at hs
      cases hs
      exact False.elim (hn hv)
  | grant hf =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | grant hs hv hp hlv =>
      rw [signatures_lookup hf] at hs
      cases hs
      dsimp only [Function.signature] at hv hp hk
      have body := (wf.function_at hf).body
      dsimp only [Function.resourceContext] at body
      rw [hv, ← loan_resource_modes] at body
      apply typed_eval body
      · simp [Function.valueContext, EnvTyped, immutable, List.map_map, hp]
      · exact .cons (.callReturn hen hlv) hk
      · exact .callReturn hlv hl
      · exact hw
  | grantMissing hf =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | grant hs hv hp hlv =>
      obtain ⟨fn, hf', _⟩ := signatures_lookup_inv hs
      rw [hf] at hf'; contradiction
  | closed hclose =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | close hkEq =>
      obtain ⟨tail, rest, ho, hr, hm, hrest⟩ := hl.owner_inv
      rw [hr] at hk
      cases hk with
      | cons hf hk =>
        cases hf
        apply typed_ret
        · exact hen
        · simpa [hr] using hk
        · exact hl.closed hclose
        · exact World.close_valid hw hclose
  | closeUnavailable hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | close hkEq =>
      obtain ⟨next, hc⟩ := hl.close_exists
      rw [hn] at hc; contradiction
  | closeWrong hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | close he =>
      exact False.elim (hn _ he)
  | revoke =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | revoke he =>
      exact .intro hen (.restore rfl) hk hl hw
  | revokeWrong hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | revoke he =>
      exact False.elim (hn _ _ _ he)
  | restore =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | restore he =>
      have hr := hl.call_inv.1
      rw [hr] at hk
      cases hk with
      | cons hf hk =>
        cases hf with
        | callReturn hcaller hv =>
          exact typed_ret hcaller hk hl.call_inv.2.2 hw
  | restoreWrong hn =>
    rcases h with ⟨hen, hc, hk, hl, hw⟩
    dsimp only at hen hc hk hl hw
    cases hc with
    | restore he =>
      exact False.elim (hn _ _ _ he)

theorem State.Typed.not_invalid (h : State.Typed p s t) : s.control ≠ .invalid := by
  rcases s with ⟨control, a, k, w⟩
  rcases h with ⟨_, hc, _, _, _⟩
  cases hc <;> intro he <;> cases he

theorem progress (h : State.Typed p s t) : Terminal s ∨ ∃ next, Step p responses s next := by
  cases hs : step p responses s with
  | some next => exact .inr ⟨next, step_sound hs⟩
  | none =>
    rcases stopped_iff.mp hs with final | invalid
    · exact .inl final
    · exact False.elim (h.not_invalid invalid)

theorem steps_preserve (wf : WellFormedProgram p) (h : State.Typed p s t)
    (hs : Steps p responses s last) : State.Typed p last t := by
  induction hs with
  | refl => exact h
  | head hs _ ih => exact ih (preservation wf h hs)

theorem safety (wf : WellFormedProgram p) (h : State.Typed p s t)
    (hs : Steps p responses s last) :
    State.Typed p last t ∧ (Terminal last ∨ ∃ next, Step p responses last next) := by
  have typed := steps_preserve wf h hs
  exact ⟨typed, progress typed⟩

theorem no_invalid (wf : WellFormedProgram p) (h : State.Typed p s t)
    (hs : Steps p responses s last) : last.control ≠ .invalid :=
  (steps_preserve wf h hs).not_invalid

theorem entry_typed (wf : WellFormedProgram p) : State.Typed p (initial p) (.scalar (.legacy .i64)) := by
  obtain ⟨fn, hf, hv, hp, ht, _⟩ := wf.entry_typed
  apply State.Typed.intro (Γ := [])
  · rfl
  · exact .invoke (signatures_lookup hf) hv hp trivial
  · simpa only [initial, Function.signature, ht] using
      (KontTyped.nil (sigs := p.signatures) (Γ := []) (resources := []) (f := p.entry) (t := fn.result))
  · exact .nil
  · exact World.initial_valid wf.profile

theorem entry_safety (wf : WellFormedProgram p) (hs : Steps p responses (initial p) last) :
    State.Typed p last (.scalar (.legacy .i64)) ∧ (Terminal last ∨ ∃ next, Step p responses last next) :=
  safety wf (entry_typed wf) hs

theorem normal_cleanup (h : State.Typed p ⟨.ret value, a, [], w⟩ t) :
    value.type = t ∧ w.owners = [] ∧ a.resources = [] := by
  rcases h with ⟨hen, hc, hk, hl, hw⟩
  cases hc
  cases hk
  obtain ⟨ho, hr⟩ := hl.nil_inv
  exact ⟨rfl, List.map_eq_nil_iff.mp ho, hr⟩

theorem normal_entry_cleanup (wf : WellFormedProgram p)
    (hs : Steps p responses (initial p) ⟨.ret value, a, [], w⟩) :
    value.type = .scalar (.legacy .i64) ∧ w.owners = [] ∧ a.resources = [] ∧
      w.positiveHeap = [] ∧ w.activeEmpties = [] := by
  obtain ⟨ht, ho, hr⟩ := normal_cleanup (steps_preserve wf (entry_typed wf) hs)
  exact ⟨ht, ho, hr, by simp [World.positiveHeap, ho], by simp [World.activeEmpties, ho]⟩

end ANL.Words
