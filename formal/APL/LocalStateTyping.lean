import APL.LocalState

namespace APL.LocalState

mutual
  inductive HasType (sigs : Signatures) : Ctx → Term → Ty → Prop where
    | lit : HasType sigs Γ (.lit v) v.type
    | local : Γ[index]? = some (t, permission) → HasType sigs Γ (.local index) t
    | letE : HasType sigs Γ a u → HasType sigs ((u, false) :: Γ) b t → HasType sigs Γ (.letE a b) t
    | letMut : HasType sigs Γ a u → HasType sigs ((u, true) :: Γ) b t → HasType sigs Γ (.letMut a b) t
    | assign : Γ[i]? = some (t, true) → HasType sigs Γ a t → HasType sigs Γ (.assign i a) .unit
    | whileE : HasType sigs Γ c .bool → HasType sigs Γ b .unit → HasType sigs Γ (.whileE c b) .unit
    | ifE : HasType sigs Γ c .bool → HasType sigs Γ a t → HasType sigs Γ b t → HasType sigs Γ (.ifE c a b) t
    | unary : HasType sigs Γ a op.input → HasType sigs Γ (.unary op a) op.output
    | binary : HasType sigs Γ a u → HasType sigs Γ b v → binaryType op u v = some t →
        HasType sigs Γ (.binary op a b) t
    | call : sigs[f]? = some (params, result) → ArgsTyped sigs Γ args params →
        HasType sigs Γ (.call f args) result
  inductive ArgsTyped (sigs : Signatures) : Ctx → List Term → List Ty → Prop where
    | nil : ArgsTyped sigs Γ [] []
    | cons : HasType sigs Γ e t → ArgsTyped sigs Γ es ts → ArgsTyped sigs Γ (e :: es) (t :: ts)
end

theorem infer_complete (h : HasType sigs Γ e t) : infer sigs Γ e = some t := by
  induction h using HasType.rec
    (motive_2 := fun Γ es ts _ => es.mapM (infer sigs Γ) = some ts) with
  | lit => simp [infer]
  | «local» h => simp [infer, h]
  | letE _ _ ha hb => simp [infer, ha, hb]
  | letMut _ _ ha hb => simp [infer, ha, hb]
  | assign hi _ ha => simp [infer, hi, ha]
  | whileE _ _ hc hb => simp [infer, hc, hb]
  | ifE _ _ _ hc ha hb => simp [infer, hc, ha, hb]
  | unary _ ha => simp [infer, ha]
  | binary _ _ hop ha hb => simp [infer, ha, hb, hop]
  | call hf _ ha => simp [infer, hf, ha]
  | nil => rfl
  | cons _ _ ha hb => simp [List.mapM_cons, ha, hb]

theorem infer_sound (h : infer sigs Γ e = some t) : HasType sigs Γ e t := by
  induction e using Term.rec
    (motive_2 := fun es => ∀ Γ ts, es.mapM (infer sigs Γ) = some ts → ArgsTyped sigs Γ es ts)
    generalizing Γ t with
  | lit v => simp [infer] at h; subst t; exact .lit
  | «local» i =>
    simp only [infer, Option.map_eq_some_iff] at h
    obtain ⟨⟨ty, permission⟩, hi, ht⟩ := h
    change ty = t at ht
    subst ty
    exact .local hi
  | letE a b ia ib =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, hb⟩ := h
    exact .letE (ia ha) (ib hb)
  | letMut a b ia ib =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, hb⟩ := h
    exact .letMut (ia ha) (ib hb)
  | assign i a ia =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨u, permission⟩, hi, v, ha, h⟩ := h
    split at h
    next ht =>
      obtain ⟨rfl, rfl⟩ := ht
      cases h
      exact .assign hi (ia ha)
    · contradiction
  | whileE c b ic ib =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨ct, hc, bt, hb, h⟩ := h
    split at h
    next ht =>
      obtain ⟨rfl, rfl⟩ := ht
      cases h
      exact .whileE (ic hc) (ib hb)
    · contradiction
  | ifE c a b ic ia ib =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨ct, hc, ta, ha, tb, hb, h⟩ := h
    split at h
    next ht =>
      obtain ⟨rfl, rfl⟩ := ht
      cases h
      exact .ifE (ic hc) (ia ha) (ib hb)
    · contradiction
  | unary op a ia =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, h⟩ := h
    split at h
    next ht => cases h; subst u; exact .unary (ia ha)
    · contradiction
  | binary op a b ia ib =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, v, hb, ht⟩ := h
    exact .binary (ia ha) (ib hb) ht
  | call f args ih =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨params, result⟩, hf, actual, ha, h⟩ := h
    split at h
    next he => cases h; subst actual; exact .call hf (ih _ _ ha)
    · contradiction
  | nil Γ ts h =>
    simp at h
    subst ts
    exact .nil
  | cons a args ia ih Γ ts h =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨t, ht, rest, hr, h⟩ := h
    cases h
    exact .cons (ia ht) (ih _ _ hr)

theorem type_unique (ha : HasType sigs Γ e a) (hb : HasType sigs Γ e b) : a = b :=
  Option.some.inj ((infer_complete ha).symm.trans (infer_complete hb))

def signatures (fs : Functions) : Signatures := fs.map fun fn => (fn.params, fn.result)

def WellTyped (fs : Functions) : Prop :=
  ∀ (f : Nat) (fn : Function), fs[f]? = some fn → HasType (signatures fs) (immutable fn.params.reverse) fn.body fn.result

theorem signatures_lookup {fs : Functions} {f : Nat} {fn : Function} (h : fs[f]? = some fn) :
    (signatures fs)[f]? = some (fn.params, fn.result) := by
  simp [signatures, Array.getElem?_map, h]

theorem signatures_lookup_inv {fs : Functions} {f : Nat} {params : List Ty} {result : Ty} (h : (signatures fs)[f]? = some (params, result)) :
    ∃ fn : Function, fs[f]? = some fn ∧ fn.params = params ∧ fn.result = result := by
  simp only [signatures, Array.getElem?_map] at h
  cases hf : fs[f]? with
  | none => simp [hf] at h
  | some fn =>
    simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨fn, rfl, h⟩

theorem checked_functions (h : ∀ (f : Nat) (fn : Function), fs[f]? = some fn →
    infer (signatures fs) (immutable fn.params.reverse) fn.body = some fn.result) : WellTyped fs := by
  intro f fn hf
  exact infer_sound (h f fn hf)


def EnvTyped (env : Env) (Γ : Ctx) : Prop := env.map Val.type = Γ.map Prod.fst

theorem env_cons (h : EnvTyped env Γ) : EnvTyped (v :: env) ((v.type, permission) :: Γ) := by
  simpa [EnvTyped] using h

theorem env_tail (h : EnvTyped (v :: env) (binding :: Γ)) : EnvTyped env Γ := by
  simpa [EnvTyped] using (List.cons.inj h).2

theorem env_lookup {i : Nat} {t : Ty} {permission : Bool} (h : EnvTyped env Γ) (hi : Γ[i]? = some (t, permission)) :
    ∃ v : Val, env[i]? = some v ∧ v.type = t := by
  have eq := congrArg (fun xs => xs[i]?) h
  simp only [List.getElem?_map, hi, Option.map_some] at eq
  cases hv : env[i]? with
  | none => simp [hv] at eq
  | some v => exact ⟨v, rfl, by simpa [hv] using eq⟩

theorem update_typed (h : EnvTyped env Γ) (hi : Γ[i]? = some (v.type, permission)) :
    ∃ env', update env i v = some env' ∧ EnvTyped env' Γ := by
  induction env generalizing Γ i with
  | nil => cases Γ <;> simp_all [EnvTyped]
  | cons a env ih =>
    cases Γ with
    | nil => simp [EnvTyped] at h
    | cons binding Γ =>
      have tail := env_tail h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst binding
        exact ⟨v :: env, rfl, env_cons tail⟩
      | succ i =>
        obtain ⟨env', hu, ht⟩ := ih tail hi
        exact ⟨a :: env', by simp [update, hu], by
          change a.type :: env'.map Val.type = binding.fst :: Γ.map Prod.fst
          rw [(List.cons.inj h).1, ht]⟩

theorem update_other (h : update env i v = some env') (different : j ≠ i) : env'[j]? = env[j]? := by
  induction env generalizing env' i j with
  | nil => simp [update] at h
  | cons a env ih =>
    cases i with
    | zero =>
      simp only [update, Option.some.injEq] at h
      subst env'
      cases j with
      | zero => exact False.elim (different rfl)
      | succ j => rfl
    | succ i =>
      simp only [update, Option.map_eq_some_iff] at h
      obtain ⟨rest, hr, rfl⟩ := h
      cases j with
      | zero => rfl
      | succ j => exact ih hr (fun eq => different (congrArg Nat.succ eq))

/-- A checked assignment cannot select any statically immutable binding. -/
theorem immutable_unchanged {Γ : Ctx} {i j : Nat} {t u : Ty} (hi : Γ[i]? = some (t, true))
    (hj : Γ[j]? = some (u, false)) (h : update env i v = some env') : env'[j]? = env[j]? := by
  apply update_other h
  intro eq
  subst j
  rw [hi] at hj
  cases hj

inductive Frame.Typed (sigs : Signatures) : Ctx → Frame → Ty → Ctx → Ty → Prop where
  | bind : HasType sigs ((a, permission) :: Γ) e b →
      Frame.Typed sigs Γ (.bind permission e) a Γ b
  | scope : Frame.Typed sigs (binding :: Γ) .scope t Γ t
  | assign : Γ[i]? = some (t, true) → Frame.Typed sigs Γ (.assign i) t Γ .unit
  | ifF : HasType sigs Γ yes t → HasType sigs Γ no t →
      Frame.Typed sigs Γ (.ifF yes no) .bool Γ t
  | unary : Frame.Typed sigs Γ (.unary op) op.input Γ op.output
  | left : HasType sigs Γ e b → binaryType op a b = some t →
      Frame.Typed sigs Γ (.left op e) a Γ t
  | right : binaryType op v.type b = some t → Frame.Typed sigs Γ (.right op v) b Γ t
  | arguments : ArgsTyped sigs Γ remaining rest →
      sigs[f]? = some ((values.map Val.type).reverse ++ a :: rest, result) →
      Frame.Typed sigs Γ (.arguments f remaining values) a Γ result
  | callReturn : EnvTyped caller Δ → Frame.Typed sigs Γ (.callReturn caller) t Δ t
  | condition : HasType sigs Γ c .bool → HasType sigs Γ b .unit →
      Frame.Typed sigs Γ (.condition c b) .bool Γ .unit
  | body : HasType sigs Γ c .bool → HasType sigs Γ b .unit →
      Frame.Typed sigs Γ (.body c b) .unit Γ .unit

inductive KontTyped (sigs : Signatures) : Ctx → List Frame → Ty → Ty → Prop where
  | nil : KontTyped sigs Γ [] t t
  | cons : Frame.Typed sigs Γ f a Δ b → KontTyped sigs Δ k b t → KontTyped sigs Γ (f :: k) a t

inductive State.Typed (sigs : Signatures) : State → Ty → Prop where
  | eval : HasType sigs Γ e a → EnvTyped env Γ → KontTyped sigs Γ k a t →
      State.Typed sigs (.eval e env k) t
  | ret : EnvTyped env Γ → KontTyped sigs Γ k v.type t → State.Typed sigs (.ret v env k) t
  | invoke : sigs[f]? = some ((values.map Val.type).reverse, result) →
      EnvTyped caller Γ → KontTyped sigs Γ k result t → State.Typed sigs (.invoke f values caller k) t
  | trap : State.Typed sigs (.trap kind) t

end APL.LocalState
