import APL.LocalStateSafety

namespace APL.LocalState

/-- Immutable cells agree, and the two environments have the same binding shape. -/
inductive Frozen : Ctx → Env → Env → Prop where
  | nil : Frozen [] [] []
  | cons : (permission = false → a = b) → Frozen Γ as bs →
      Frozen ((t, permission) :: Γ) (a :: as) (b :: bs)

theorem frozen_refl (ht : EnvTyped env Γ) : Frozen Γ env env := by
  induction Γ generalizing env with
  | nil =>
    cases env with
    | nil => exact .nil
    | cons _ _ => simp [EnvTyped] at ht
  | cons binding Γ ih =>
    cases env with
    | nil => simp [EnvTyped] at ht
    | cons v env =>
      cases binding
      exact .cons (fun _ => rfl) (ih (env_tail ht))

private def projectFrame (frame : Frame) (env : Env) : Env :=
  match frame with
  | .scope => env.tail
  | .callReturn caller => caller
  | _ => env

private theorem frame_frozen (ht : Frame.Typed sigs Γ frame a Δ b) (hf : Frozen Γ before after) :
    Frozen Δ (projectFrame frame before) (projectFrame frame after) := by
  cases ht <;> try exact hf
  case scope => cases hf; assumption
  case callReturn hen => exact frozen_refl hen

private inductive ContextFrames (sigs : Signatures) : Ctx → List Frame → Ctx → Prop where
  | nil : ContextFrames sigs Γ [] Γ
  | cons : Frame.Typed sigs Γ frame a Δ b → ContextFrames sigs Δ rest final →
      ContextFrames sigs Γ (frame :: rest) final

private def projectFrames (env : Env) : List Frame → Env
  | [] => env
  | frame :: rest => projectFrames (projectFrame frame env) rest

private theorem frames_frozen (ht : ContextFrames sigs Γ frames Δ) (hf : Frozen Γ before after) :
    Frozen Δ (projectFrames before frames) (projectFrames after frames) := by
  induction ht generalizing before after with
  | nil => exact hf
  | cons ht _ ih => exact ih (frame_frozen ht hf)

theorem frozen_trans (ha : Frozen Γ a b) (hb : Frozen Γ b c) : Frozen Γ a c := by
  induction ha generalizing c with
  | nil => cases hb; exact .nil
  | cons he _ ih =>
    cases hb with
    | cons he' ht => exact .cons (fun hp => (he hp).trans (he' hp)) (ih ht)

theorem update_frozen (hen : EnvTyped env Γ) (hi : Γ[i]? = some (v.type, true))
    (hu : update env i v = some env') : Frozen Γ env env' := by
  induction env generalizing Γ i env' with
  | nil => simp [update] at hu
  | cons a env ih =>
    cases Γ with
    | nil => simp [EnvTyped] at hen
    | cons binding Γ =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst binding
        simp only [update, Option.some.injEq] at hu
        subst env'
        exact .cons (by intro h; contradiction) (frozen_refl (env_tail hen))
      | succ i =>
        simp only [update, Option.map_eq_some_iff] at hu
        obtain ⟨rest, hr, rfl⟩ := hu
        cases binding
        exact .cons (fun _ => rfl) (ih (env_tail hen) hi hr)

private inductive RootKont (sigs : Signatures) :
    Ctx → List Frame → Ty → Ctx → Ty → Prop where
  | nil : RootKont sigs Γ [] t Γ t
  | cons : Frame.Typed sigs Γ f a Δ b → RootKont sigs Δ k b root t →
      RootKont sigs Γ (f :: k) a root t

private theorem root_context (ht : RootKont sigs Γ k a root t) : ContextFrames sigs Γ k root := by
  induction ht with
  | nil => exact .nil
  | cons hf _ ih => exact .cons hf ih

private inductive Tracked (sigs : Signatures) (root : Ctx) (entry : Env) :
    State → Ty → Prop where
  | eval : HasType sigs Γ e a → EnvTyped env Γ → RootKont sigs Γ k a root t →
      Frozen root entry (projectFrames env k) → Tracked sigs root entry (.eval e env k) t
  | ret : EnvTyped env Γ → RootKont sigs Γ k v.type root t →
      Frozen root entry (projectFrames env k) → Tracked sigs root entry (.ret v env k) t
  | invoke : sigs[f]? = some ((values.map Val.type).reverse, result) →
      EnvTyped caller Γ → RootKont sigs Γ k result root t →
      Frozen root entry (projectFrames caller k) → Tracked sigs root entry (.invoke f values caller k) t
  | trap : Tracked sigs root entry (.trap kind) t

private theorem resume_tracked (h : r.Typed a) (he : EnvTyped env Γ)
    (hk : RootKont sigs Γ k a root t) (hf : Frozen root entry (projectFrames env k)) :
    Tracked sigs root entry (resume r env k) t := by
  cases r with
  | value v => exact .ret he (by simpa [Result.Typed] using h ▸ hk) hf
  | trap kind => exact .trap
  | invalid => exact False.elim h

private theorem tracked_preservation (wf : WellTyped fs)
    (h : Tracked (signatures fs) root entry s t)
    (hs : Step fs s s') : Tracked (signatures fs) root entry s' t := by
  cases hs with
  | lit => cases h with | eval he hen hk hf => cases he; exact .ret hen hk hf
  | localFound hv =>
    cases h with
    | eval he hen hk hf =>
      cases he with
      | «local» ht =>
        obtain ⟨v, hv', ht⟩ := env_lookup hen ht
        rw [hv] at hv'
        cases hv'
        exact .ret hen (ht ▸ hk) hf
  | localMissing hv =>
    cases h with
    | eval he hen hk hf =>
      cases he with
      | «local» ht =>
        obtain ⟨v, hv', _⟩ := env_lookup hen ht
        rw [hv] at hv'
        contradiction
  | letEval =>
    cases h with | eval he hen hk hf => cases he with | letE ha hb => exact .eval ha hen (.cons (.bind hb) hk) hf
  | letMutEval =>
    cases h with | eval he hen hk hf => cases he with | letMut ha hb => exact .eval ha hen (.cons (.bind hb) hk) hf
  | bindReturn =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | bind hb => exact .eval hb (env_cons hen) (.cons .scope hk) hf
  | scopeReturn =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe; exact .ret (env_tail hen) hk hf
  | scopeMissing =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe; simp [EnvTyped] at hen
  | assignEval =>
    cases h with | eval he hen hk hf => cases he with | assign hi ha => exact .eval ha hen (.cons (.assign hi) hk) hf
  | assignReturn hu =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | assign hi =>
      obtain ⟨env', hu', ht⟩ := update_typed hen hi
      rw [hu] at hu'
      cases hu'
      have changed := frames_frozen (root_context hk) (update_frozen hen hi hu)
      exact .ret ht hk (frozen_trans hf changed)
  | assignMissing hu =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | assign hi =>
      obtain ⟨env', hu', ht⟩ := update_typed hen hi
      rw [hu] at hu'
      contradiction
  | ifEval =>
    cases h with | eval he hen hk hf => cases he with | ifE hc ha hb => exact .eval hc hen (.cons (.ifF ha hb) hk) hf
  | unaryEval =>
    cases h with | eval he hen hk hf => cases he with | unary ha => exact .eval ha hen (.cons .unary hk) hf
  | binaryEval =>
    cases h with | eval he hen hk hf => cases he with | binary ha hb hop => exact .eval ha hen (.cons (.left hb hop) hk) hf
  | ifTrue =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with | ifF ha hb => exact .eval ha hen hk hf
  | ifFalse =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with | ifF ha hb => exact .eval hb hen hk hf
  | ifInt => cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe
  | ifUnit => cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe
  | unaryReturn =>
    cases h with
    | ret hen hk hf =>
      generalize hv : Val.type _ = a at hk
      cases hk with
      | cons hframe hk => cases hframe; exact resume_tracked (unary_typed hv) hen hk hf
  | short hs =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | left hb hop => exact .ret hen ((shortCircuit_typed hop hs) ▸ hk) hf
  | rightEval =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | left hb hop => exact .eval hb hen (.cons (.right hop) hk) hf
  | binaryReturn =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | right hop => exact resume_tracked (binary_typed hop) hen hk hf
  | callEmpty =>
    cases h with | eval he hen hk hf => cases he with | call hfunc ha => cases ha; exact .invoke hfunc hen hk hf
  | callFirst =>
    cases h with | eval he hen hk hf => cases he with | call hfunc ha => cases ha with
    | cons ha hs => exact .eval ha hen (.cons (.arguments hs hfunc) hk) hf
  | argumentNext =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | arguments ha hfunc =>
      cases ha with
      | cons ha hs =>
        exact .eval ha hen (.cons (.arguments hs (by simpa [List.reverse_cons, List.append_assoc] using hfunc)) hk) hf
  | argumentsDone =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | arguments ha hfunc =>
      cases ha
      exact .invoke (by simpa [List.reverse_cons] using hfunc) hen hk hf
  | invoke hfunc =>
    cases h with
    | invoke hs hen hk hf =>
      have sig := signatures_lookup hfunc
      rw [sig] at hs
      have eq := (Prod.mk.inj (Option.some.inj hs)).1
      have result := (Prod.mk.inj (Option.some.inj hs)).2
      have body := wf _ _ hfunc
      rw [eq, List.reverse_reverse, result] at body
      exact .eval body (by simp [EnvTyped, immutable, List.map_map])
        (.cons (.callReturn hen) hk) hf
  | invalidFunction hfunc =>
    cases h with
    | invoke hs hen hk hf =>
      obtain ⟨fn, hfunc', _, _⟩ := signatures_lookup_inv hs
      rw [hfunc] at hfunc'
      contradiction
  | callReturn =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | callReturn hcaller => exact .ret hcaller hk hf
  | whileEval =>
    cases h with | eval he hen hk hf => cases he with | whileE hc hb => exact .eval hc hen (.cons (.condition hc hb) hk) hf
  | whileTrue =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | condition hc hb => exact .eval hb hen (.cons (.body hc hb) hk) hf
  | whileFalse =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | condition hc hb => exact .ret hen hk hf
  | whileInt => cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe
  | whileUnit => cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe
  | whileAgain =>
    cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe with
    | body hc hb => exact .eval hc hen (.cons (.condition hc hb) hk) hf
  | bodyInt => cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe
  | bodyBool => cases h with | ret hen hk hf => cases hk with | cons hframe hk => cases hframe

private theorem tracked_steps (wf : WellTyped fs)
    (ht : Tracked (signatures fs) root entry s t)
    (hs : Steps fs s last) : Tracked (signatures fs) root entry last t := by
  induction hs with
  | refl => exact ht
  | head hstep _ ih => exact ih (tracked_preservation wf ht hstep)

/-- A complete typed evaluation preserves immutable cells, including through nested
scopes, calls, and loops. This does not assert that evaluation terminates. -/
theorem evaluation_frame (wf : WellTyped fs)
    (ht : HasType (signatures fs) Γ e t)
    (hen : EnvTyped env Γ)
    (hs : Steps fs (.eval e env []) (.ret v env' [])) : Frozen Γ env env' ∧ EnvTyped env' Γ ∧ v.type = t := by
  have initial : Tracked (signatures fs) Γ env (.eval e env []) t :=
    .eval ht hen .nil (frozen_refl hen)
  have last := tracked_steps wf initial hs
  cases last with
  | ret hen hk hf => cases hk; exact ⟨hf, hen, rfl⟩


private def appendKont (suffix : List Frame) : State → State
  | .eval e env k => .eval e env (k ++ suffix)
  | .ret v env k => .ret v env (k ++ suffix)
  | .invoke f values env k => .invoke f values env (k ++ suffix)
  | .trap kind => .trap kind
  | .invalid => .invalid

private theorem append_resume : appendKont suffix (resume r env k) = resume r env (k ++ suffix) := by
  cases r <;> rfl

private theorem append_step (hs : Step fs s s') : Step fs (appendKont suffix s) (appendKont suffix s') := by
  apply step_sound
  cases hs <;> simp_all [step, appendKont]
  all_goals exact append_resume.symm

/-- The expression has returned, and its outer continuation has not run yet. -/
def AtReturn (suffix : List Frame) (s : State) : Prop := ∃ v env, s = .ret v env suffix

private theorem append_pullback (hs : Step fs (appendKont suffix s) last)
    (hb : ¬ AtReturn suffix (appendKont suffix s)) :
    ∃ next, Step fs s next ∧ last = appendKont suffix next := by
  cases hstep : step fs s with
  | some next =>
    exact ⟨next, step_sound hstep, deterministic hs (append_step (step_sound hstep))⟩
  | none =>
    cases s with
    | eval e env k => simp [step] at hstep
    | invoke f values env k => simp [step] at hstep
    | ret v env k =>
      cases k with
      | nil => exact False.elim (hb ⟨v, env, rfl⟩)
      | cons frame rest => simp [step] at hstep
    | trap kind => have impossible := step_complete hs; simp [appendKont, step] at impossible
    | invalid => have impossible := step_complete hs; simp [appendKont, step] at impossible

private theorem append_return (he : appendKont suffix s = .ret v env suffix) : s = .ret v env [] := by
  cases s with
  | eval e env k => cases he
  | invoke f values env k => cases he
  | trap kind => cases he
  | invalid => cases he
  | ret w initial k =>
    simp only [appendKont, State.ret.injEq] at he
    obtain ⟨rfl, rfl, hk⟩ := he
    have hlen := congrArg List.length hk
    simp only [List.length_append] at hlen
    have hz : k.length = 0 := by omega
    cases k with
    | nil => rfl
    | cons _ _ => simp at hz

/-- An actual machine prefix that cannot cross a return to the given suffix.
Equality of the initial and final continuation alone does not impose this boundary. -/
inductive FirstReturn (fs : Functions) (suffix : List Frame) : State → Val → Env → Prop where
  | done : FirstReturn fs suffix (.ret v env suffix) v env
  | next : ¬ AtReturn suffix s → Step fs s s' → FirstReturn fs suffix s' v env →
      FirstReturn fs suffix s v env

theorem first_return_steps (h : FirstReturn fs suffix s v env) : Steps fs s (.ret v env suffix) := by
  induction h with
  | done => exact .refl
  | next _ hs _ ih => exact .head hs ih

private theorem first_return_erase (h : FirstReturn fs suffix s v env)
    (he : s = appendKont suffix initial) : FirstReturn fs [] initial v env := by
  induction h generalizing initial with
  | done =>
    have same := append_return he.symm
    subst initial
    exact .done
  | next hb hs _ ih =>
    rw [he] at hb hs
    obtain ⟨next, hstep, hlast⟩ := append_pullback hs hb
    refine .next ?_ hstep (ih hlast)
    rintro ⟨value, values, hi⟩
    subst initial
    exact hb ⟨value, values, rfl⟩

theorem first_return_isolated (h : FirstReturn fs suffix (.eval e env suffix) v final) :
    Steps fs (.eval e env []) (.ret v final []) :=
  first_return_steps (first_return_erase h rfl)

/-- The first return stops before the caller continuation can run. -/
theorem first_return_frame (wf : WellTyped fs)
    (ht : HasType (signatures fs) Γ e t) (hen : EnvTyped env Γ)
    (hr : FirstReturn fs suffix (.eval e env suffix) v final) :
    Frozen Γ env final ∧ EnvTyped final Γ ∧ v.type = t :=
  evaluation_frame wf ht hen (first_return_isolated hr)

-- Equal continuations can recur after an outer loop recreates a local binding.
private def transitions (fs : Functions) : Nat → State → Option State
  | 0, state => some state
  | n + 1, state => (step fs state).bind (transitions fs n)

private theorem transitions_steps (h : transitions fs n s = some last) : Steps fs s last := by
  induction n generalizing s with
  | zero => cases h; exact .refl
  | succ n ih =>
    simp only [transitions, Option.bind_eq_some_iff] at h
    obtain ⟨next, hs, hrest⟩ := h
    exact .head (step_sound hs) (ih hrest)

private def zero : Val := .int ⟨0, by decide⟩
private def one : Val := .int ⟨1, by decide⟩
private def condition : Term := .letE
  (.assign 0 (.binary .add (.local 0) (.lit one))) (.lit (.bool true))
private def body : Term := .letE (.local 0) (.lit .unit)
private def outer : List Frame := [.scope, .body condition body]
private def localContext : Ctx := [(.i64, false), (.i64, true)]

example : HasType #[] [(.i64, true)] condition .bool := by
  apply infer_sound
  simp [condition, infer, one, Val.type, binaryType]

example : HasType #[] [(.i64, true)] body .unit := by
  apply infer_sound
  simp [body, infer, Val.type]

example : State.Typed #[] (.eval (.lit .unit) [zero, zero] outer) .unit := by
  apply State.Typed.eval (Γ := localContext) HasType.lit
  · rfl
  · apply KontTyped.cons Frame.Typed.scope
    apply KontTyped.cons (Frame.Typed.body ?_ ?_) KontTyped.nil
    · apply infer_sound
      simp [condition, infer, one, Val.type, binaryType]
    · apply infer_sound
      simp [body, infer, Val.type]

private theorem repeated_continuation_changes_snapshot :
    Steps #[] (.eval (.lit .unit) [zero, zero] outer) (.ret .unit [one, one] outer) := by
  apply transitions_steps (n := 19)
  rfl

example : ([zero, zero] : Env)[0]? ≠ ([one, one] : Env)[0]? := by decide

end APL.LocalState
