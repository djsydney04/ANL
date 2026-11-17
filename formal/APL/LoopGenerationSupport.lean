import APL.LoopVCGSoundness

/-! Shape and syntactic-instantiation support for sufficient-height generation.
No symbolic denotation, formula validity or runtime safety premise is required. -/

namespace APL.LoopGeneration
open VCG LoopVCG LoopAnnotations

/-- Result-free static precondition syntax; no truth or definedness premise. -/
inductive PreType (types : List Ty) : Spec → Ty → Prop where
  | lit : PreType types (.lit v) v.type
  | param : types[i]? = some ty → PreType types (.param i) ty
  | unary : PreType types a op.input → PreType types (.unary op a) op.output
  | binary : PreType types a u → PreType types b v → binaryType op u v = some t →
      PreType types (.binary op a b) t

def PreconditionsTyped (fs : Functions) (pre : Preconditions) : Prop :=
  ∀ f fn, fs[f]? = some fn → ∀ clause ∈ pre f, PreType fn.params clause .bool

theorem lookup_exists {xs : List α} (h : i < xs.length) : ∃ x, xs[i]? = some x :=
  ⟨xs[i], List.getElem?_eq_getElem h⟩

theorem pre_instantiate (h : PreType types clause ty) (hlen : syms.length = types.length) :
    ∃ term, clause.instantiate syms none = some term := by
  induction h with
  | lit => exact ⟨_, rfl⟩
  | param hi =>
    have bound := (List.getElem?_eq_some_iff.mp hi).1
    exact lookup_exists (hlen ▸ bound)
  | unary _ ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨_, by simp [Spec.instantiate, ha] <;> rfl⟩
  | binary _ _ _ ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    exact ⟨_, by simp [Spec.instantiate, ha, hb] <;> rfl⟩

theorem requires_total
    (ht : ∀ clause ∈ clauses, PreType types clause .bool)
    (hlen : syms.length = types.length) : ∃ pair, requiresVC syms clauses = some pair := by
  induction clauses with
  | nil => exact ⟨_, rfl⟩
  | cons c cs ih =>
    obtain ⟨s, hs⟩ := pre_instantiate (ht c (by simp)) hlen
    obtain ⟨⟨d, t⟩, hr⟩ := ih (fun x hx => ht x (by simp [hx]))
    exact ⟨_, by simp [requiresVC, hs, hr] <;> rfl⟩

theorem assertion_total (ht : Assertion.HasType Γ clause ty)
    (hlen : syms.length = Γ.length) : ∃ term, clause.instantiate syms = some term := by
  induction ht with
  | lit => exact ⟨_, rfl⟩
  | «local» hi =>
    have bound := (List.getElem?_eq_some_iff.mp hi).1
    exact lookup_exists (hlen ▸ bound)
  | unary _ ih =>
    obtain ⟨a, ha⟩ := ih
    simp only [Assertion.instantiate] at ha
    exact ⟨_, by simp only [Assertion.instantiate, Assertion.toSpec, Spec.instantiate,
      ha, bind, Option.bind_some, Option.pure_def]; rfl⟩
  | binary _ _ _ ia ib =>
    obtain ⟨a, ha⟩ := ia
    obtain ⟨b, hb⟩ := ib
    simp only [Assertion.instantiate] at ha
    simp only [Assertion.instantiate] at hb
    exact ⟨_, by simp only [Assertion.instantiate, Assertion.toSpec, Spec.instantiate,
      ha, hb, bind, Option.bind_some, Option.pure_def]; rfl⟩

theorem assertions_total (ht : ∀ clause ∈ clauses, Assertion.HasType Γ clause .bool)
    (hlen : syms.length = Γ.length) : ∃ pair, assertions syms path clauses = some pair := by
  induction clauses with
  | nil => exact ⟨_, rfl⟩
  | cons c cs ih =>
    obtain ⟨s, hs⟩ := assertion_total (ht c (by simp)) hlen
    obtain ⟨⟨checks, truth⟩, hr⟩ := ih (fun x hx => ht x (by simp [hx]))
    exact ⟨_, by simp [assertions, hs, hr] <;> rfl⟩

def Shape (n : Nat) (a : Analysis α) : Prop :=
  ∀ out ∈ a.outcomes, out.env.length = n

theorem shape_single (he : env.length = n) : Shape n (single value env path next) := by
  intro out member
  simp only [single, List.mem_singleton] at member
  subst out
  exact he

theorem shape_combine (ha : Shape n a) (hb : Shape n b) : Shape n (combine a b) := by
  intro out member
  rcases List.mem_append.mp member with h | h
  · exact ha out h
  · exact hb out h

theorem sequence_total
    (ha : ∀ out ∈ outcomes, ∀ next, ∃ result, action out next = some result ∧ Shape n result) :
    ∀ next, ∃ result, sequence action outcomes next = some result ∧ Shape n result := by
  induction outcomes with
  | nil => intro next; exact ⟨_, rfl, by intro _ h; cases h⟩
  | cons out rest ih =>
    intro next
    obtain ⟨first, hf, hfirst⟩ := ha out (by simp) next
    obtain ⟨tail, ht, htail⟩ := ih (fun x hx => ha x (by simp [hx])) first.next
    exact ⟨_, by simp [sequence, hf, ht], shape_combine hfirst htail⟩

theorem bind_total {input : Analysis α} {action : Outcome α → Nat → Option (Analysis β)}
    (ha : ∀ out ∈ input.outcomes, ∀ next, ∃ result, action out next = some result ∧ Shape n result) :
    ∃ result, bindAnalysis input action = some result ∧ Shape n result := by
  obtain ⟨later, hl, hs⟩ := sequence_total ha input.next
  exact ⟨{ later with checks := input.checks ++ later.checks }, by simp [bindAnalysis, hl], hs⟩

theorem update_total (h : i < env.length) :
    ∃ updated, StateVCG.updateSymbols env i value = some updated ∧ updated.length = env.length := by
  induction env generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => exact ⟨_, rfl, rfl⟩
    | succ i =>
      obtain ⟨tail, ht, hl⟩ := ih (by simpa using h)
      exact ⟨_, by simp [StateVCG.updateSymbols, ht] <;> rfl, by simp [hl]⟩

theorem fresh_total (hlen : syms.length = Γ.length) :
    ∃ head finish, freshEnv Γ syms start = some (head, finish) ∧ head.length = Γ.length := by
  induction Γ generalizing syms start with
  | nil =>
    have he : syms = [] := List.length_eq_zero_iff.mp hlen
    subst syms
    exact ⟨_, _, rfl, rfl⟩
  | cons cell Γ ih =>
    cases syms with
    | nil => simp at hlen
    | cons s ss =>
      obtain ⟨ty, mutable⟩ := cell
      have htail : ss.length = Γ.length := by simpa using hlen
      cases mutable with
      | false =>
        obtain ⟨tail, finish, hf, hl⟩ := ih (start := start) htail
        exact ⟨s :: tail, finish, by simp [freshEnv, hf], by simp [hl]⟩
      | true =>
        cases ty with
        | unit =>
          obtain ⟨tail, finish, hf, hl⟩ := ih (start := start) htail
          exact ⟨.lit .unit :: tail, finish, by simp [freshEnv, hf], by simp [hl]⟩
        | i64 | bool =>
          obtain ⟨tail, finish, hf, hl⟩ := ih (start := start + 1) htail
          exact ⟨.var start :: tail, finish, by simp [freshEnv, hf], by simp [hl]⟩

theorem domain_total (hlen : syms.length = Γ.length) : ∃ domain, headDomain Γ syms = some domain := by
  induction Γ generalizing syms with
  | nil =>
    have he : syms = [] := List.length_eq_zero_iff.mp hlen
    subst syms
    exact ⟨_, rfl⟩
  | cons cell Γ ih =>
    cases syms with
    | nil => simp at hlen
    | cons s ss =>
      obtain ⟨domain, hd⟩ := ih (by simpa using hlen)
      exact ⟨_, by simp [headDomain, hd] <;> rfl⟩

theorem head_total (hlen : syms.length = Γ.length) :
    ∃ head, freshHead Γ syms start = some head ∧ head.symbols.length = Γ.length := by
  obtain ⟨head, finish, hf, hl⟩ := fresh_total (start := start) hlen
  obtain ⟨domain, hd⟩ := domain_total hl
  exact ⟨_, by simp [freshHead, hf, hd] <;> rfl, hl⟩

end APL.LoopGeneration

namespace APL.LoopGeneration
open VCG LoopVCG LoopAnnotations

def Results (P : Outcome α → Prop) (a : Analysis α) : Prop := ∀ out ∈ a.outcomes, P out

theorem sequence_results {action : Outcome α → Nat → Option (Analysis β)}
    (ha : ∀ out ∈ outcomes, ∀ next, ∃ result, action out next = some result ∧ Results P result) :
    ∀ next, ∃ result, sequence action outcomes next = some result ∧ Results P result := by
  induction outcomes with
  | nil => intro next; exact ⟨_, rfl, by intro _ h; cases h⟩
  | cons out rest ih =>
    intro next
    obtain ⟨first, hf, hfirst⟩ := ha out (by simp) next
    obtain ⟨tail, ht, htail⟩ := ih (fun x hx => ha x (by simp [hx])) first.next
    refine ⟨combine first tail, by simp [sequence, hf, ht], ?_⟩
    intro out member
    rcases List.mem_append.mp member with h | h
    · exact hfirst out h
    · exact htail out h

theorem bind_results {input : Analysis α} {action : Outcome α → Nat → Option (Analysis β)}
    (ha : ∀ out ∈ input.outcomes, ∀ next, ∃ result, action out next = some result ∧ Results P result) :
    ∃ result, bindAnalysis input action = some result ∧ Results P result := by
  obtain ⟨later, hl, hs⟩ := sequence_results ha input.next
  exact ⟨{ later with checks := input.checks ++ later.checks }, by simp [bindAnalysis, hl], hs⟩

theorem arguments_total
    (ha : ∀ arg ∈ args, ∀ env path next, env.length = n →
      ∃ result, generate arg env path next = some result ∧ Shape n result)
    (hlen : env.length = n) :
    ∃ result, arguments generate args env path next = some result ∧
      Results (fun out => out.env.length = n ∧ out.value.length = args.length) result := by
  induction args generalizing env path next with
  | nil =>
    refine ⟨_, rfl, ?_⟩
    intro out member
    simp only [single, List.mem_singleton] at member
    subst out
    exact ⟨hlen, rfl⟩
  | cons arg rest ih =>
    obtain ⟨first, hf, hs⟩ := ha arg (by simp) env path next hlen
    simp only [arguments, hf, bind, Option.bind_some]
    apply bind_results
    intro out member next
    obtain ⟨remaining, hr, hremain⟩ := ih (path := out.path) (next := next) (fun a hm => ha a (by simp [hm])) (hs out member)
    refine ⟨{ remaining with outcomes := remaining.outcomes.map fun r =>
      ⟨out.value :: r.value, r.env, r.path⟩ }, by simp [hr], ?_⟩
    intro r hmember
    obtain ⟨prior, hp, rfl⟩ := List.mem_map.mp hmember
    have prop := hremain prior hp
    exact ⟨prop.1, by simp [prop.2]⟩

theorem pop_total {outs : List (Outcome SymTerm)}
    (hs : ∀ out ∈ outs, out.env.length = n + 1) :
    ∃ popped, outs.mapM (fun result => do
      let _ ← result.env.head?
      pure { result with env := result.env.tail }) = some popped ∧
      ∀ out ∈ popped, out.env.length = n := by
  induction outs with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons out rest ih =>
    obtain ⟨tail, ht, htail⟩ := ih (fun x hx => hs x (by simp [hx]))
    have hlen := hs out (by simp)
    obtain ⟨value, env, path⟩ := out
    cases env with
    | nil => simp at hlen
    | cons s ss =>
      refine ⟨⟨value, ss, path⟩ :: tail, ?_, ?_⟩
      · simp only [bind, Option.pure_def] at ht
        simp only [List.mapM_cons, List.head?_cons, bind, Option.bind_some,
          List.tail_cons, Option.pure_def, ht]
      · intro result hm
        rcases List.mem_cons.mp hm with rfl | hrest
        · simpa using hlen
        · exact htail result hrest

end APL.LoopGeneration
