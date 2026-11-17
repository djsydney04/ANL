import APL.VCG

namespace APL.VCG

inductive Spec where
  | lit (v : MVal)
  | param (index : Nat)
  | result
  | unary (op : UOp) (a : Spec)
  | binary (op : BOp) (a b : Spec)
  deriving Repr

def Spec.eval (params : List MVal) (result : Option MVal) : Spec → Option MVal
  | .lit v => some v
  | .param i => params[i]?
  | .result => result
  | .unary op a => do mUnary op (← a.eval params result)
  | .binary op a b => do
    let va ← a.eval params result
    if mShort op va then some va else mBinary op va (← b.eval params result)

def Spec.instantiate (params : List SymTerm) (result : Option SymTerm) : Spec → Option SymTerm
  | .lit v => some (.lit v)
  | .param i => params[i]?
  | .result => result
  | .unary op a => return .unary op (← a.instantiate params result)
  | .binary op a b => return .binary op (← a.instantiate params result) (← b.instantiate params result)

def ResultRep (model : Model) : Option SymTerm → Option Val → Prop
  | none, none => True
  | some s, some v => Denotes model s v
  | _, _ => False

theorem instantiate_sound {spec : Spec} {s : SymTerm} (h : spec.instantiate syms result = some s)
    (hp : EnvRep model syms params) (hr : ResultRep model result value) :
    s.eval model = spec.eval (params.map embed) (value.map embed) := by
  induction spec generalizing s with
  | lit v => cases h; rfl
  | param i =>
    obtain ⟨v, hv, hd⟩ := EnvRep.lookup hp h
    simpa [Spec.eval, List.getElem?_map, hv, Denotes] using hd
  | result =>
    cases result with
    | none => contradiction
    | some term =>
      cases h
      cases value with
      | none => contradiction
      | some v => exact hr
  | unary op a ia =>
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨a', ha, h⟩ := h
    cases h
    simp [SymTerm.eval, Spec.eval, ia ha]
  | binary op a b ia ib =>
    simp only [Spec.instantiate, bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨a', ha, b', hb, h⟩ := h
    cases h
    simp [SymTerm.eval, Spec.eval, ia ha, ib hb]

def specPost (params : List SymTerm) (spec : Spec) : Post := fun result => do
  let s ← spec.instantiate params (some result)
  pure (.holds s)

theorem spec_post_sound (h : PostHolds model (specPost syms spec) result)
    (hp : EnvRep model syms params) :
    spec.eval (params.map embed) (some (embed result)) = some (.bool true) := by
  obtain ⟨s, f, hf, hvalid, hd⟩ := h
  simp only [specPost, bind, Option.bind_eq_some_iff, Option.pure_def] at hf
  obtain ⟨inst, hi, hf⟩ := hf
  cases hf
  exact (instantiate_sound (value := some result) hi hp hd).symm.trans hvalid

private theorem env_append (ha : EnvRep model a va) (hb : EnvRep model b vb) :
    EnvRep model (a ++ b) (va ++ vb) := by
  induction ha with
  | nil => exact hb
  | cons h _ ih => exact .cons h ih

theorem env_reverse (h : EnvRep model syms env) : EnvRep model syms.reverse env.reverse := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => simpa only [List.reverse_cons] using env_append ih (.cons h .nil)

private theorem env_of_lookup (hlen : syms.length = env.length)
    (h : ∀ (i : Nat) s v, syms[i]? = some s → env[i]? = some v → Denotes model s v) :
    EnvRep model syms env := by
  induction syms generalizing env with
  | nil => cases env with
    | nil => exact .nil
    | cons _ _ => cases hlen
  | cons s ss ih =>
    cases env with
    | nil => cases hlen
    | cons v vs =>
      exact .cons (h 0 s v rfl rfl) (ih (Nat.succ.inj hlen) (fun i a b ha hb => h (i+1) a b ha hb))

def parameterSymbols (n : Nat) : List SymTerm := (List.range n).map SymTerm.var

def modelOf (params : Env) : Model := fun i => (params[i]?.map embed).getD .unit

private theorem parameter_symbols_rep (params : Env) :
    EnvRep (modelOf params) (parameterSymbols params.length) params := by
  apply env_of_lookup (by simp [parameterSymbols])
  intro i s v hs hv
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hv
  simp only [parameterSymbols, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.some.injEq] at hs
  subst s
  simp [Denotes, SymTerm.eval, modelOf, hv]

def RequiresDefined (params : List MVal) : List Spec → Prop
  | [] => True
  | c :: cs => (∃ b, c.eval params none = some (.bool b)) ∧
      (c.eval params none = some (.bool true) → RequiresDefined params cs)

def RequiresHold (params : List MVal) : List Spec → Prop
  | [] => True
  | c :: cs => c.eval params none = some (.bool true) ∧ RequiresHold params cs

def requiresVC (syms : List SymTerm) : List Spec → Option (Formula × Formula)
  | [] => some (.truth true, .truth true)
  | c :: cs => do
    let s ← c.instantiate syms none
    let (defined, truth) ← requiresVC syms cs
    return (.and (.boolean s) (.imp (.holds s) defined), .and (.holds s) truth)

theorem requires_vc_sound (h : requiresVC syms clauses = some (defined, truth))
    (hp : EnvRep model syms params) :
    (defined.Holds model ↔ RequiresDefined (params.map embed) clauses) ∧
    (truth.Holds model ↔ RequiresHold (params.map embed) clauses) := by
  induction clauses generalizing defined truth with
  | nil => cases h; simp [Formula.Holds, RequiresDefined, RequiresHold]
  | cons c cs ih =>
    simp only [requiresVC, bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨s, hs, ⟨d, t⟩, htail, he⟩ := h
    cases he
    have heval := instantiate_sound (value := none) hs hp (by trivial)
    have ih := ih htail
    simp [Formula.Holds, RequiresDefined, RequiresHold, heval, ih.1, ih.2]

structure ContractVC where
  requiresDefined : Formula
  requiresTruth : Formula
  body : Formula
  deriving Repr

def generateContract (params : List Ty) (body : Program.Term) (preconditions : List Spec) (post : Spec) :
    Option ContractVC := do
  let syms := parameterSymbols params.length
  let (defined, truth) ← requiresVC syms preconditions
  let formula ← wp body syms.reverse (specPost syms post)
  return ⟨defined, truth, formula⟩

def Accepted (types : List Ty) (vc : ContractVC) : Prop :=
  (∀ params : Env, params.map Val.type = types → vc.requiresDefined.Holds (modelOf params)) ∧
  (∃ params : Env, params.map Val.type = types ∧ vc.requiresTruth.Holds (modelOf params)) ∧
  (∀ params : Env, params.map Val.type = types → vc.requiresTruth.Holds (modelOf params) →
    vc.body.Holds (modelOf params))

theorem typed_parameters_rep {params : Env} (h : params.map Val.type = types) :
    EnvRep (modelOf params) (parameterSymbols types.length) params := by
  have hlen := congrArg List.length h
  simp only [List.length_map] at hlen
  rw [← hlen]
  exact parameter_symbols_rep params

private theorem safe_mono (h : Safe p out) (hp : ∀ v, p v → q v) : Safe q out := by
  cases out with
  | ok pair => exact hp pair.1 h
  | error err => cases err with
    | resourceLimit => trivial
    | trap _ | invalid => exact h

theorem contract_eval_sound {params : Env} (hgen : generateContract types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions) :
    Safe (fun v => post.eval (params.map embed) (some (embed v)) = some (.bool true))
      (Program.eval fs depth params.reverse body fuel) := by
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, formula, hwp, hgen⟩ := hgen
  cases hgen
  have hp := typed_parameters_rep ht
  have htruth := ((requires_vc_sound hrequires hp).2).mpr hpre
  have hvalid := ha.2.2 params ht htruth
  have hs := wp_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hwp (env_reverse hp) hvalid
  exact safe_mono hs (fun _ h => spec_post_sound h hp)

theorem contract_preconditions_defined {params : Env} (hgen : generateContract types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types) :
    RequiresDefined (params.map embed) preconditions := by
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, formula, hwp, hgen⟩ := hgen
  cases hgen
  exact ((requires_vc_sound hrequires (typed_parameters_rep ht)).1).mp (ha.1 params ht)

theorem contract_nonvacuous (hgen : generateContract types body preconditions post = some vc)
    (ha : Accepted types vc) : ∃ params : Env, params.map Val.type = types ∧ RequiresHold (params.map embed) preconditions := by
  obtain ⟨params, ht, htruth⟩ := ha.2.1
  simp only [generateContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, formula, hwp, hgen⟩ := hgen
  cases hgen
  exact ⟨params, ht, ((requires_vc_sound hrequires (typed_parameters_rep ht)).2).mp htruth⟩

theorem contract_steps_value {params : Env}
    (hgen : generateContract types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions)
    (hs : Program.Steps fs (.eval body params.reverse []) (.ret v [])) :
    post.eval (params.map embed) (some (embed v)) = some (.bool true) := by
  obtain ⟨depth, fuel, remaining, he⟩ := Program.eval_value_complete hs
  have h := contract_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hgen ha ht hpre
  simpa only [he, Safe] using h

theorem contract_steps_no_trap {params : Env}
    (hgen : generateContract types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions) :
    ¬ Program.Steps fs (.eval body params.reverse []) (.trap kind) := by
  intro hs
  obtain ⟨depth, fuel, he⟩ := Program.eval_trap_complete hs
  have h := contract_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hgen ha ht hpre
  simp only [he, Safe] at h

theorem contract_steps_no_invalid {params : Env}
    (hgen : generateContract types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions) :
    ¬ Program.Steps fs (.eval body params.reverse []) .invalid := by
  intro hs
  obtain ⟨depth, fuel, he⟩ := Program.eval_invalid_complete hs
  have h := contract_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hgen ha ht hpre
  simp only [he, Safe] at h

namespace Examples

private def one : Val := .int ⟨1, by decide⟩
private def incBody : Program.Term := .binary .add (.local 0) (.lit one)
private def incReq : Spec := .binary .lt (.param 0) (.lit (.int maxI64))
private def incPost : Spec := .binary .eq .result (.binary .add (.param 0) (.lit (.int 1)))
private def incVC : ContractVC := {
  requiresDefined := .and (.boolean (.binary .lt (.var 0) (.lit (.int maxI64))))
    (.imp (.holds (.binary .lt (.var 0) (.lit (.int maxI64)))) (.truth true)),
  requiresTruth := .and (.holds (.binary .lt (.var 0) (.lit (.int maxI64)))) (.truth true),
  body := .and (.range (.binary .add (.var 0) (.lit (.int 1))))
    (.holds (.binary .eq (.binary .add (.var 0) (.lit (.int 1))) (.binary .add (.var 0) (.lit (.int 1))))) }

example : generateContract [.i64] incBody [incReq] incPost = some incVC := by
  simp [generateContract, parameterSymbols, requiresVC, Spec.instantiate, wp, incBody, incReq, incPost,
    one, embed, shortable, binaryWP, binaryGuard, specPost, incVC]

private theorem singleton_integer (h : params.map Val.type = [.i64]) : ∃ n, params = [.int n] := by
  cases params with
  | nil => contradiction
  | cons v rest =>
    cases rest with
    | cons _ _ => simp at h
    | nil => cases v with
      | int n => exact ⟨n, rfl⟩
      | bool _ | unit => simp [Val.type] at h

example : Accepted [.i64] incVC := by
  constructor
  · intro params ht
    obtain ⟨n, rfl⟩ := singleton_integer ht
    simp [incVC, Formula.Holds, SymTerm.eval, modelOf, mShort, mBinary, embed]
  · constructor
    · exact ⟨[.int ⟨0, by decide⟩], rfl, by simp [incVC, Formula.Holds, SymTerm.eval, modelOf, mShort, mBinary, embed, maxI64]⟩
    · intro params ht hpre
      obtain ⟨n, rfl⟩ := singleton_integer ht
      simp [incVC, Formula.Holds, SymTerm.eval, modelOf, mShort, mBinary, embed] at hpre ⊢
      have hn := n.property
      unfold InRange at hn ⊢
      omega

example : Spec.eval [] none (.binary .div (.lit (.int minI64)) (.lit (.int (-1)))) =
    some (.int 9223372036854775808) := by decide

example : Spec.eval [] none (.binary .or (.lit (.bool true))
    (.binary .eq (.binary .div (.lit (.int 1)) (.lit (.int 0))) (.lit (.int 0)))) = some (.bool true) := by decide

example : wp (.ifE (.lit (.bool true)) (.lit .unit) (.call 0 [])) []
    (fun _ => some (.truth true)) = none := by simp [wp]

example (hgen : generateContract [] (.lit .unit) [.lit (.bool false)] (.lit (.bool true)) = some vc) :
    ¬ Accepted [] vc := by
  intro ha
  obtain ⟨params, _, hpre⟩ := contract_nonvacuous hgen ha
  simp [RequiresHold, Spec.eval] at hpre

example (hgen : generateContract [] (.lit .unit)
    [.binary .eq (.binary .div (.lit (.int 1)) (.lit (.int 0))) (.lit (.int 0))]
    (.lit (.bool true)) = some vc) : ¬ Accepted [] vc := by
  intro ha
  have h := contract_preconditions_defined (params := []) hgen ha rfl
  simp [RequiresDefined, Spec.eval, mShort, mBinary] at h

private def maximum : Val := .int ⟨maxI64, by decide⟩
private def minimum : Val := .int ⟨minI64, by decide⟩
private def minusOne : Val := .int ⟨-1, by decide⟩

example (hwp : wp (.letE (.binary .add (.lit maximum) (.lit one)) (.lit .unit)) []
    (fun _ => some (.truth true)) = some formula) : ¬ formula.Holds model := by
  simp [wp, binaryWP, binaryGuard, shortable, maximum, one, embed] at hwp
  cases hwp
  simp [Formula.Holds, SymTerm.eval, mShort, mBinary, InRange, maxI64]

example (hwp : wp (.binary .rem (.lit minimum) (.lit minusOne)) []
    (fun _ => some (.truth true)) = some formula) : ¬ formula.Holds model := by
  simp [wp, binaryWP, binaryGuard, shortable, minimum, minusOne, embed] at hwp
  cases hwp
  simp [Formula.Holds, divisionGuard, SymTerm.eval, mShort, mBinary, MVal.type]

example : ∃ formula, wp (.binary .and (.lit (.bool false))
    (.binary .eq (.binary .div (.lit one) (.lit (.int ⟨0, by decide⟩))) (.lit one))) []
      (fun _ => some (.truth true)) = some formula ∧ formula.Holds model := by
  simp [wp, binaryWP, binaryGuard, divisionGuard, shortable, shortGuard,
    one, embed, Formula.Holds, SymTerm.eval, mShort, mUnary, mBinary]

example : Spec.eval [] none (.binary .div (.lit (.int (-7))) (.lit (.int 3))) = some (.int (-2)) := by decide
example : Spec.eval [] none (.binary .rem (.lit (.int (-7))) (.lit (.int 3))) = some (.int (-1)) := by decide

private def zero : Val := .int ⟨0, by decide⟩
private def seven : Val := .int ⟨7, by decide⟩
private def heteroBody : Program.Term := .ifE (.local 2) (.local 1) (.lit zero)
private def heteroPost : Spec := .binary .and (.binary .eq .result (.param 1))
  (.binary .eq (.param 2) (.lit .unit))
private def heteroPostTerm (result : SymTerm) : SymTerm :=
  .binary .and (.binary .eq result (.var 1)) (.binary .eq (.var 2) (.lit .unit))
private def heteroVC : ContractVC := {
  requiresDefined := .and (.boolean (.var 0)) (.imp (.holds (.var 0)) (.truth true)),
  requiresTruth := .and (.holds (.var 0)) (.truth true),
  body := .and (.boolean (.var 0)) (.and
    (.imp (.holds (.var 0)) (.holds (heteroPostTerm (.var 1))))
    (.imp (.holds (.unary .not (.var 0))) (.holds (heteroPostTerm (.lit (.int 0)))))) }

private theorem hetero_generated : generateContract [.bool, .i64, .unit] heteroBody [.param 0] heteroPost = some heteroVC := by
  simp [generateContract, parameterSymbols, requiresVC, Spec.instantiate, wp, heteroBody, heteroPost,
    zero, embed, specPost, heteroVC, heteroPostTerm]

private theorem heterogeneous_parameters {params : Env} (h : params.map Val.type = [.bool, .i64, .unit]) :
    ∃ b n, params = [.bool b, .int n, .unit] := by
  cases params with
  | nil => contradiction
  | cons a rest =>
    cases rest with
    | nil => simp at h
    | cons b rest =>
      cases rest with
      | nil => simp at h
      | cons c rest =>
        cases rest with
        | cons _ _ => simp at h
        | nil => cases a <;> cases b <;> cases c <;> simp_all [Val.type]

private theorem hetero_accepted : Accepted [.bool, .i64, .unit] heteroVC := by
  constructor
  · intro params ht
    obtain ⟨b, n, rfl⟩ := heterogeneous_parameters ht
    simp [heteroVC, Formula.Holds, SymTerm.eval, modelOf, embed]
  · constructor
    · exact ⟨[.bool true, zero, .unit], rfl, by
        simp [heteroVC, Formula.Holds, SymTerm.eval, modelOf, embed]⟩
    · intro params ht hpre
      obtain ⟨b, n, rfl⟩ := heterogeneous_parameters ht
      cases b <;> simp_all [heteroVC, heteroPostTerm, Formula.Holds, SymTerm.eval,
        modelOf, embed, mShort, mBinary, mUnary, MVal.type]

example : Program.eval #[] 3 [.unit, seven, .bool true] heteroBody 5 = .ok (seven, 2) := by rfl

example : heteroPost.eval [.bool true, .int 7, .unit] (some (.int 7)) = some (.bool true) := by
  have hpre : RequiresHold (([.bool true, seven, .unit] : Env).map embed) [.param 0] := by
    simp [RequiresHold, Spec.eval, embed]
  have hs := contract_eval_sound (fs := #[]) (depth := 3) (fuel := 5)
    hetero_generated hetero_accepted (params := [.bool true, seven, .unit]) rfl hpre
  have he : Program.eval #[] 3 [.unit, seven, .bool true] heteroBody 5 = .ok (seven, 2) := by rfl
  change Safe (fun v => heteroPost.eval [.bool true, .int 7, .unit] (some (embed v)) = some (.bool true))
    (Program.eval #[] 3 [.unit, seven, .bool true] heteroBody 5) at hs
  rw [he] at hs
  exact hs

end Examples
end APL.VCG
