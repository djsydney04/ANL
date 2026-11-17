import APL.Core

namespace APL

inductive Frame where
  | letF (env : Env) (body : Expr)
  | ifF (env : Env) (yes no : Expr)
  | unary (op : UOp)
  | left (op : BOp) (env : Env) (right : Expr)
  | right (op : BOp) (left : Val)
  deriving Repr

abbrev Kont := List Frame

inductive State where
  | eval (expr : Expr) (env : Env) (kont : Kont)
  | ret (value : Val) (kont : Kont)
  | trap (kind : Trap)
  | invalid
  deriving Repr

def resume (r : Result) (k : Kont) : State :=
  match r with
  | .value v => .ret v k
  | .trap t => .trap t
  | .invalid => .invalid

def shortCircuit (op : BOp) (v : Val) : Bool :=
  match op, v with
  | .and, .bool false | .or, .bool true => true
  | _, _ => false

def step : State → Option State
  | .eval (.lit v) _ k => some (.ret v k)
  | .eval (.local i) env k => some (match env[i]? with | some v => .ret v k | none => .invalid)
  | .eval (.letE a b) env k => some (.eval a env (.letF env b :: k))
  | .eval (.ifE c a b) env k => some (.eval c env (.ifF env a b :: k))
  | .eval (.unary op a) env k => some (.eval a env (.unary op :: k))
  | .eval (.binary op a b) env k => some (.eval a env (.left op env b :: k))
  | .ret v (.letF env b :: k) => some (.eval b (v :: env) k)
  | .ret (.bool b) (.ifF env a c :: k) => some (.eval (if b then a else c) env k)
  | .ret _ (.ifF _ _ _ :: _) => some .invalid
  | .ret v (.unary op :: k) => some (resume (unary op v) k)
  | .ret v (.left op env b :: k) =>
      some (if shortCircuit op v then .ret v k else .eval b env (.right op v :: k))
  | .ret v (.right op a :: k) => some (resume (binary op a v) k)
  | .ret _ [] | .trap _ | .invalid => none

inductive Frame.Typed : Frame → Ty → Ty → Prop where
  | letF : HasType (a :: env.map Val.type) body b → Frame.Typed (.letF env body) a b
  | ifF : HasType (env.map Val.type) yes t → HasType (env.map Val.type) no t →
      Frame.Typed (.ifF env yes no) .bool t
  | unary : Frame.Typed (.unary op) op.input op.output
  | left : HasType (env.map Val.type) e b → binaryType op a b = some t →
      Frame.Typed (.left op env e) a t
  | right : binaryType op v.type b = some t → Frame.Typed (.right op v) b t

inductive Kont.Typed : Kont → Ty → Ty → Prop where
  | nil : Kont.Typed [] t t
  | cons : Frame.Typed f a b → Kont.Typed k b t → Kont.Typed (f :: k) a t

inductive State.Typed : State → Ty → Prop where
  | eval : HasType (env.map Val.type) e a → Kont.Typed k a t → State.Typed (.eval e env k) t
  | ret : Kont.Typed k v.type t → State.Typed (.ret v k) t
  | trap : State.Typed (.trap kind) t

theorem lookup_typed {env : Env} {i : Nat} {t : Ty} (h : (env.map Val.type)[i]? = some t) :
    ∃ v, env[i]? = some v ∧ v.type = t := by
  simp only [List.getElem?_map] at h
  cases hv : env[i]? with
  | none => simp [hv] at h
  | some v => exact ⟨v, rfl, by simpa [hv] using h⟩

theorem resume_typed (h : r.Typed a) (hk : k.Typed a t) : (resume r k).Typed t := by
  cases r with
  | value v => exact .ret (by simpa [Result.Typed] using h ▸ hk)
  | trap kind => exact .trap
  | invalid => exact False.elim h

theorem shortCircuit_typed (h : binaryType op v.type b = some t)
    (hs : shortCircuit op v = true) : v.type = t := by
  cases op <;> cases v <;> cases b <;> simp_all [shortCircuit, binaryType, Val.type]

theorem step_preserves (h : s.Typed t) (hs : step s = some s') : s'.Typed t := by
  cases h with
  | eval he hk =>
    cases he with
    | lit => cases hs; exact .ret hk
    | «local» hv =>
      obtain ⟨v, hv, ht⟩ := lookup_typed hv
      simp [step, hv] at hs
      subst s'
      exact .ret (ht ▸ hk)
    | letE ha hb =>
      cases hs
      exact .eval ha (.cons (.letF hb) hk)
    | ifE hc ha hb =>
      cases hs
      exact .eval hc (.cons (.ifF ha hb) hk)
    | unary ha =>
      cases hs
      exact .eval ha (.cons .unary hk)
    | binary ha hb hop =>
      cases hs
      exact .eval ha (.cons (.left hb hop) hk)
  | @ret k t v hk =>
    generalize hv : v.type = a at hk
    cases hk with
    | nil => simp [step] at hs
    | cons hf hk =>
      cases hf with
      | letF hb =>
        cases hs
        exact .eval (by simpa [hv] using hb) hk
      | ifF ha hb =>
        cases v with
        | int v | unit => contradiction
        | bool b =>
          cases b <;> cases hs
          · exact .eval hb hk
          · exact .eval ha hk
      | unary =>
        cases hs
        exact resume_typed (unary_typed hv) hk
      | left hb hop =>
        simp only [step, Option.some.injEq] at hs
        split at hs
        next hh =>
          subst s'
          exact .ret ((shortCircuit_typed (hv ▸ hop) hh) ▸ hk)
        next =>
          subst s'
          exact .eval hb (.cons (.right (hv ▸ hop)) hk)
      | right hop =>
        cases hs
        exact resume_typed (binary_typed (hv ▸ hop)) hk
  | trap => simp [step] at hs

inductive Terminal : State → Prop where
  | value : Terminal (.ret v [])
  | trap : Terminal (.trap kind)

theorem progress (h : s.Typed t) : Terminal s ∨ ∃ s', step s = some s' := by
  cases h with
  | eval he hk => cases he <;> exact Or.inr ⟨_, rfl⟩
  | @ret k t v hk =>
    cases k with
    | nil => exact Or.inl .value
    | cons f k =>
      cases f <;> try exact Or.inr ⟨_, rfl⟩
      cases v <;> exact Or.inr ⟨_, rfl⟩
  | trap => exact Or.inl .trap

end APL
