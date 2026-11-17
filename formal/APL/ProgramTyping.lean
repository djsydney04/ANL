import APL.ProgramSemantics

namespace APL.Program

mutual
  inductive HasType (sigs : Signatures) : Ctx → Term → Ty → Prop where
    | lit : HasType sigs Γ (.lit v) v.type
    | local : Γ[index]? = some t → HasType sigs Γ (.local index) t
    | letE : HasType sigs Γ a u → HasType sigs (u :: Γ) b t → HasType sigs Γ (.letE a b) t
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
  | «local» h => simpa [infer] using h
  | letE _ _ ha hb => simp [infer, ha, hb]
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
  | «local» i => exact .local (by simpa [infer] using h)
  | letE a b ia ib =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, hb⟩ := h
    exact .letE (ia ha) (ib hb)
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
  ∀ (f : Nat) (fn : Function), fs[f]? = some fn → HasType (signatures fs) fn.params.reverse fn.body fn.result

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
    infer (signatures fs) fn.params.reverse fn.body = some fn.result) : WellTyped fs := by
  intro f fn hf
  exact infer_sound (h f fn hf)

inductive Frame.Typed (sigs : Signatures) : Frame → Ty → Ty → Prop where
  | letF : HasType sigs (a :: env.map Val.type) body b → Frame.Typed sigs (.letF env body) a b
  | ifF : HasType sigs (env.map Val.type) yes t → HasType sigs (env.map Val.type) no t →
      Frame.Typed sigs (.ifF env yes no) .bool t
  | unary : Frame.Typed sigs (.unary op) op.input op.output
  | left : HasType sigs (env.map Val.type) e b → binaryType op a b = some t →
      Frame.Typed sigs (.left op env e) a t
  | right : binaryType op v.type b = some t → Frame.Typed sigs (.right op v) b t
  | arguments : ArgsTyped sigs (caller.map Val.type) remaining rest →
      sigs[f]? = some ((values.map Val.type).reverse ++ a :: rest, result) →
      Frame.Typed sigs (.arguments f caller remaining values) a result

inductive KontTyped (sigs : Signatures) : List Frame → Ty → Ty → Prop where
  | nil : KontTyped sigs [] t t
  | cons : Frame.Typed sigs f a b → KontTyped sigs k b t → KontTyped sigs (f :: k) a t

inductive State.Typed (sigs : Signatures) : State → Ty → Prop where
  | eval : HasType sigs (env.map Val.type) e a → KontTyped sigs k a t →
      State.Typed sigs (.eval e env k) t
  | ret : KontTyped sigs k v.type t → State.Typed sigs (.ret v k) t
  | invoke : sigs[f]? = some ((values.map Val.type).reverse, result) →
      KontTyped sigs k result t → State.Typed sigs (.invoke f values k) t
  | trap : State.Typed sigs (.trap kind) t

end APL.Program
