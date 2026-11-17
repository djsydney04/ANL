import APL.ProgramEvalCompleteness
namespace APL.VCG

inductive MVal where
  | int (n : Int)
  | bool (b : Bool)
  | unit
  deriving DecidableEq, Repr

def MVal.type : MVal → Ty
  | .int _ => .i64
  | .bool _ => .bool
  | .unit => .unit

def embed : Val → MVal
  | .int n => .int n.val
  | .bool b => .bool b
  | .unit => .unit

private theorem embed_inj : embed a = embed b ↔ a = b := by
  cases a <;> cases b <;> simp [embed, Subtype.ext_iff]

def mUnary : UOp → MVal → Option MVal
  | .neg, .int n => some (.int (-n))
  | .not, .bool b => some (.bool (!b))
  | _, _ => none

def mBinary : BOp → MVal → MVal → Option MVal
  | .add, .int a, .int b => some (.int (a+b))
  | .sub, .int a, .int b => some (.int (a-b))
  | .mul, .int a, .int b => some (.int (a*b))
  | .div, .int a, .int b => if b = 0 then none else some (.int (quotient a b))
  | .rem, .int a, .int b => if b = 0 then none else some (.int (a-quotient a b*b))
  | .lt, .int a, .int b => some (.bool (a < b))
  | .le, .int a, .int b => some (.bool (a ≤ b))
  | .gt, .int a, .int b => some (.bool (a > b))
  | .ge, .int a, .int b => some (.bool (a ≥ b))
  | .eq, a, b => if a.type = b.type then some (.bool (a=b)) else none
  | .ne, a, b => if a.type = b.type then some (.bool (a != b)) else none
  | .and, .bool a, .bool b => some (.bool (a && b))
  | .or, .bool a, .bool b => some (.bool (a || b))
  | _, _, _ => none

def mShort : BOp → MVal → Bool
  | .and, .bool false | .or, .bool true => true
  | _, _ => false

inductive SymTerm where
  | lit (v : MVal)
  | var (index : Nat)
  | unary (op : UOp) (a : SymTerm)
  | binary (op : BOp) (a b : SymTerm)
  deriving Repr

abbrev Model := Nat → MVal

def SymTerm.eval (model : Model) : SymTerm → Option MVal
  | .lit v => some v
  | .var i => some (model i)
  | .unary op a => do mUnary op (← a.eval model)
  | .binary op a b => do
    let va ← a.eval model
    if mShort op va then some va else mBinary op va (← b.eval model)

inductive Formula where
  | truth (b : Bool)
  | holds (e : SymTerm)
  | defined (e : SymTerm)
  | boolean (e : SymTerm)
  | range (e : SymTerm)
  | and (a b : Formula)
  | not (a : Formula)
  | imp (a b : Formula)
  deriving Repr

def Formula.Holds (model : Model) : Formula → Prop
  | .truth b => b = true
  | .holds e => e.eval model = some (.bool true)
  | .defined e => ∃ v, e.eval model = some v
  | .boolean e => ∃ b, e.eval model = some (.bool b)
  | .range e => ∃ n, e.eval model = some (.int n) ∧ InRange n
  | .and a b => a.Holds model ∧ b.Holds model
  | .not a => ¬ a.Holds model
  | .imp a b => a.Holds model → b.Holds model

def Denotes (model : Model) (s : SymTerm) (v : Val) : Prop := s.eval model = some (embed v)
inductive EnvRep (model : Model) : List SymTerm → Env → Prop where
  | nil : EnvRep model [] []
  | cons : Denotes model s v → EnvRep model ss vs → EnvRep model (s :: ss) (v :: vs)

def unaryGuard (op : UOp) (a : SymTerm) : Formula :=
  match op with
  | .neg => .range (.unary op a)
  | .not => .defined (.unary op a)

def divisionGuard (a b : SymTerm) : Formula :=
  .and (.holds (.binary .ne b (.lit (.int 0))))
    (.not (.and (.holds (.binary .eq a (.lit (.int minI64))))
      (.holds (.binary .eq b (.lit (.int (-1)))))))

def binaryGuard (op : BOp) (a b : SymTerm) : Formula :=
  match op with
  | .add | .sub | .mul => .range (.binary op a b)
  | .div | .rem => .and (divisionGuard a b) (.range (.binary op a b))
  | _ => .defined (.binary op a b)

def shortGuard (op : BOp) (a : SymTerm) : Formula :=
  match op with
  | .and => .holds (.unary .not a)
  | .or => .holds a
  | _ => .truth false

def shortable : BOp → Bool
  | .and | .or => true
  | _ => false

abbrev Post := SymTerm → Option Formula

def unaryWP (op : UOp) (a : SymTerm) (post : Post) : Option Formula := do
  let q ← post (.unary op a)
  return .and (unaryGuard op a) q

def binaryWP (op : BOp) (a b : SymTerm) (post : Post) : Option Formula := do
  let q ← post (.binary op a b)
  return .and (binaryGuard op a b) q

def wp : Program.Term → List SymTerm → Post → Option Formula
  | .lit v, _, post => post (.lit (embed v))
  | .local i, env, post => env[i]?.bind post
  | .letE a b, env, post => wp a env (fun v => wp b (v :: env) post)
  | .ifE c a b, env, post => wp c env fun v => do
      let yes ← wp a env post
      let no ← wp b env post
      return .and (.boolean v) (.and (.imp (.holds v) yes) (.imp (.holds (.unary .not v)) no))
  | .unary op a, env, post => wp a env (fun v => unaryWP op v post)
  | .binary op a b, env, post => wp a env fun va =>
      let rhs := wp b env (fun vb => binaryWP op va vb post)
      if shortable op then do
        let rest ← rhs
        let skip ← post va
        return .and (.imp (shortGuard op va) skip) (.imp (.not (shortGuard op va)) rest)
      else rhs
  | .call _ _, _, _ => none

private theorem mShort_embed : mShort op (embed v) = shortCircuit op v := by
  cases op <;> cases v <;> try rfl
  all_goals cases ‹Bool› <;> rfl

theorem short_guard (h : Denotes model a v) :
    (shortGuard op a).Holds model ↔ shortCircuit op v = true := by
  cases op <;> cases v <;> simp_all [shortGuard, Formula.Holds, SymTerm.eval, Denotes, embed, mUnary, shortCircuit]
  all_goals cases ‹Bool› <;> rfl

theorem not_shortable (h : shortable op = false) : shortCircuit op v = false := by
  cases op <;> cases v <;> simp_all [shortable, shortCircuit]

private theorem sym_unary_eval (h : Denotes model a v) :
    (.unary op a : SymTerm).eval model = mUnary op (embed v) := by
  simp [SymTerm.eval, Denotes] at h ⊢
  simp [h]

private theorem sym_binary_eval (ha : Denotes model a va) (hb : Denotes model b vb)
    (hs : shortCircuit op va = false) :
    (.binary op a b : SymTerm).eval model = mBinary op (embed va) (embed vb) := by
  simp only [SymTerm.eval]
  rw [ha, hb]
  simp [mShort_embed, hs]

def MVal.Representable : MVal → Prop
  | .int n => InRange n
  | .bool _ | .unit => True

private theorem checked_lift (h : InRange n) : ∃ v, checked n = .value v ∧ embed v = .int n := by
  exact ⟨.int ⟨n, h⟩, by simp [checked, h], rfl⟩

private theorem unary_lift (h : mUnary op (embed v) = some mv) (hr : mv.Representable) :
    ∃ result, unary op v = .value result ∧ embed result = mv := by
  cases op <;> cases v <;> simp only [embed, mUnary, Option.some.injEq, reduceCtorEq] at h
  · cases h; exact checked_lift hr
  · cases h; exact ⟨_, rfl, rfl⟩

private theorem unary_guard_sound (hr : Denotes model a v) (hg : (unaryGuard op a).Holds model) :
    ∃ result, unary op v = .value result ∧ Denotes model (.unary op a) result := by
  have he := sym_unary_eval (op := op) hr
  cases op with
  | neg =>
    obtain ⟨n, hn, hb⟩ := hg
    obtain ⟨result, hres, hm⟩ := unary_lift (he.symm.trans hn) hb
    exact ⟨result, hres, hn.trans (congrArg some hm.symm)⟩
  | not =>
    obtain ⟨mv, hm⟩ := hg
    have rep : mv.Representable := by
      cases v <;> simp only [embed, mUnary] at he
      all_goals rw [he] at hm
      all_goals simp only [Option.some.injEq, reduceCtorEq] at hm
      cases hm
      trivial
    obtain ⟨result, hres, hv⟩ := unary_lift (he.symm.trans hm) rep
    exact ⟨result, hres, hm.trans (congrArg some hv.symm)⟩

def DivisionAllowed (op : BOp) (a b : Val) : Prop :=
  match op, a, b with
  | .div, .int a, .int b | .rem, .int a, .int b => ¬ (a.val = minI64 ∧ b.val = -1)
  | _, _, _ => True

private theorem binary_lift (h : mBinary op (embed va) (embed vb) = some mv)
    (hr : mv.Representable) (hd : DivisionAllowed op va vb) :
    ∃ result, binary op va vb = .value result ∧ embed result = mv := by
  cases op <;> cases va <;> cases vb <;>
    simp_all only [embed, mBinary, MVal.type, Option.some.injEq, reduceCtorEq, ite_true, ite_false]
  all_goals try (cases h; exact checked_lift hr)
  all_goals try (cases h; exact ⟨_, rfl, rfl⟩)
  case div.int.int a b =>
    split at h
    · contradiction
    next hn =>
      cases h
      simp only [DivisionAllowed] at hd
      simpa [binary, division, hn, hd, embed] using checked_lift hr
  case rem.int.int a b =>
    split at h
    · contradiction
    next hn =>
      cases h
      simp only [DivisionAllowed] at hd
      simpa [binary, division, hn, hd, embed] using checked_lift hr
  all_goals cases h
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals simp [Subtype.ext_iff]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp [bne_iff_ne, Subtype.ext_iff]

private theorem division_guard_allowed (ha : Denotes model a va) (hb : Denotes model b vb)
    (hg : (divisionGuard a b).Holds model) : DivisionAllowed op va vb := by
  cases op <;> cases va <;> cases vb <;> try trivial
  all_goals
    intro pair
    unfold Denotes at ha hb
    apply hg.2
    rcases pair with ⟨hmin, hneg⟩
    constructor
    · simp [Formula.Holds, SymTerm.eval, ha, embed, mShort, mBinary, MVal.type, hmin]
    · simp [Formula.Holds, SymTerm.eval, hb, embed, mShort, mBinary, MVal.type, hneg]

private theorem binary_guard_sound (ha : Denotes model a va) (hb : Denotes model b vb)
    (hs : shortCircuit op va = false) (hg : (binaryGuard op a b).Holds model) :
    ∃ result, binary op va vb = .value result ∧ Denotes model (.binary op a b) result := by
  have he := sym_binary_eval ha hb hs
  cases op with
  | add | sub | mul =>
    obtain ⟨n, hn, hb⟩ := hg
    obtain ⟨result, hres, hm⟩ := binary_lift (he.symm.trans hn) hb (by trivial)
    exact ⟨result, hres, hn.trans (congrArg some hm.symm)⟩
  | div | rem =>
    obtain ⟨hd, n, hn, hr⟩ := hg
    obtain ⟨result, hres, hm⟩ := binary_lift (he.symm.trans hn) hr (division_guard_allowed ha hb hd)
    exact ⟨result, hres, hn.trans (congrArg some hm.symm)⟩
  | lt | le | gt | ge | eq | ne | and | or =>
    obtain ⟨mv, hm⟩ := hg
    have mat := he.symm.trans hm
    have rep : mv.Representable := by
      cases va <;> cases vb <;>
        simp_all only [embed, mBinary, MVal.type, Option.some.injEq, reduceCtorEq, ite_true, ite_false]
      all_goals subst mv; trivial
    obtain ⟨result, hres, hv⟩ := binary_lift mat rep (by trivial)
    exact ⟨result, hres, hm.trans (congrArg some hv.symm)⟩

def PostHolds (model : Model) (post : Post) (v : Val) : Prop :=
  ∃ s formula, post s = some formula ∧ formula.Holds model ∧ Denotes model s v

def Safe (post : Val → Prop) : Except Program.Error (Val × Nat) → Prop
  | .ok (v, _) => post v
  | .error .resourceLimit => True
  | .error (.trap _) | .error .invalid => False

private theorem bind_apply (x : Program.EvalM α) (f : α → Program.EvalM β) (n : Nat) :
    (x >>= f) n = match x n with
    | .ok (v, n') => f v n'
    | .error err => .error err := by
  change (Except.bind (x n) _) = _
  cases x n with
  | error err => rfl
  | ok p => cases p; rfl

private theorem fuel_succ : Program.takeFuel (f+1) = .ok ((), f) := by rfl

private theorem fuel_then (x : Program.EvalM α) : (Program.takeFuel >>= fun _ => x) (f+1) = x f := by
  rw [bind_apply, fuel_succ]

private theorem safe_bind (x : Program.EvalM Val) (f : Val → Program.EvalM Val)
    (hx : Safe p (x fuel)) (hf : ∀ v n, p v → Safe q (f v n)) :
    Safe q ((x >>= f) fuel) := by
  rw [bind_apply]
  cases he : x fuel with
  | error err =>
    cases err with
    | resourceLimit => trivial
    | trap _ | invalid => simp only [he, Safe] at hx
  | ok pair =>
    obtain ⟨v, n⟩ := pair
    exact hf v n (by simpa only [he, Safe] using hx)

theorem EnvRep.lookup {i : Nat} (h : EnvRep model syms env) (hs : syms[i]? = some s) :
    ∃ v, env[i]? = some v ∧ Denotes model s v := by
  induction h generalizing i with
  | nil => simp at hs
  | cons hv h ih =>
    cases i with
    | zero => simp at hs; subst s; exact ⟨_, rfl, hv⟩
    | succ i => exact ih hs

theorem unary_wp_sound (h : unaryWP op a post = some formula)
    (hf : formula.Holds model) (ha : Denotes model a v) :
    Safe (PostHolds model post) (Program.liftResult (unary op v) fuel) := by
  simp only [unaryWP, bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨q, hq, he⟩ := h
  cases he
  obtain ⟨result, hr, hd⟩ := unary_guard_sound ha hf.1
  rw [hr]
  exact ⟨.unary op a, q, hq, hf.2, hd⟩

theorem binary_wp_sound (h : binaryWP op a b post = some formula)
    (hf : formula.Holds model) (ha : Denotes model a va) (hb : Denotes model b vb)
    (hs : shortCircuit op va = false) :
    Safe (PostHolds model post) (Program.liftResult (binary op va vb) fuel) := by
  simp only [binaryWP, bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨q, hq, he⟩ := h
  cases he
  obtain ⟨result, hr, hd⟩ := binary_guard_sound ha hb hs hf.1
  rw [hr]
  exact ⟨.binary op a b, q, hq, hf.2, hd⟩

theorem wp_eval_sound (hwp : wp e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    Safe (PostHolds model post) (Program.eval fs depth env e fuel) := by
  induction e using Program.Term.rec (motive_2 := fun _ => True)
    generalizing syms post formula env depth fuel
  case nil => trivial
  case cons => trivial
  all_goals cases depth
  all_goals try trivial
  all_goals cases fuel
  all_goals try (rw [Program.eval.eq_def]; trivial)
  all_goals rw [Program.eval.eq_def]; dsimp only; rw [fuel_then]
  all_goals simp only [wp] at hwp
  case lit.succ.succ v depth fuel =>
    exact ⟨.lit (embed v), formula, hwp, hformula, rfl⟩
  case «local».succ.succ i depth fuel =>
    simp only [Option.bind_eq_some_iff] at hwp
    obtain ⟨s, hs, hq⟩ := hwp
    obtain ⟨v, hv, hd⟩ := EnvRep.lookup henv hs
    rw [hv]
    exact ⟨s, formula, hq, hformula, hd⟩
  case letE.succ.succ a b ia ib depth fuel =>
    apply safe_bind _ _ (ia hwp henv hformula)
    intro v n hv
    obtain ⟨s, f, hf, hvalid, hdenotes⟩ := hv
    exact ib hf (.cons hdenotes henv) hvalid
  case ifE.succ.succ c a b ic ia ib depth fuel =>
    apply safe_bind _ _ (ic hwp henv hformula)
    intro v n hv
    obtain ⟨s, f, hf, hvalid, hdenotes⟩ := hv
    simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at hf
    obtain ⟨yes, hyes, no, hno, he⟩ := hf
    cases he
    obtain ⟨test, ht⟩ := hvalid.1
    rw [hdenotes] at ht
    cases v with
    | int _ | unit => simp [embed] at ht
    | bool test' =>
      cases ht
      unfold Denotes at hdenotes
      cases test with
      | false =>
        apply ib hno henv
        apply hvalid.2.2
        simp [Formula.Holds, SymTerm.eval, hdenotes, embed, mUnary]
      | true => exact ia hyes henv (hvalid.2.1 hdenotes)
  case unary.succ.succ op a ia depth fuel =>
    apply safe_bind _ _ (ia hwp henv hformula)
    intro v n hv
    obtain ⟨s, f, hf, hvalid, hdenotes⟩ := hv
    exact unary_wp_sound hf hvalid hdenotes
  case binary.succ.succ op a b ia ib depth fuel =>
    apply safe_bind _ _ (ia hwp henv hformula)
    intro va n hv
    obtain ⟨sa, f, hf, hvalid, hdenotes⟩ := hv
    cases hop : shortable op with
    | false =>
      simp only [hop, Bool.false_eq_true, ite_false] at hf
      have hs := not_shortable (v := va) hop
      simp only [hs, Bool.false_eq_true, ite_false]
      apply safe_bind _ _ (ib hf henv hvalid)
      intro vb n' hv
      obtain ⟨sb, g, hg, hvalid', hdenotes'⟩ := hv
      exact binary_wp_sound hg hvalid' hdenotes hdenotes' hs
    | true =>
      simp only [hop, ite_true, bind, Option.bind_eq_some_iff, Option.pure_def] at hf
      obtain ⟨rest, hrest, skip, hskip, he⟩ := hf
      cases he
      cases hs : shortCircuit op va with
      | true =>
        exact ⟨sa, skip, hskip, hvalid.1 ((short_guard hdenotes).mpr hs), hdenotes⟩
      | false =>
        apply safe_bind _ _ (ib hrest henv (hvalid.2 (by
          intro hshort
          have := (short_guard hdenotes).mp hshort
          rw [hs] at this
          contradiction)))
        intro vb n' hv
        obtain ⟨sb, g, hg, hvalid', hdenotes'⟩ := hv
        exact binary_wp_sound hg hvalid' hdenotes hdenotes' hs

theorem wp_value (hwp : wp e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model)
    (he : Program.eval fs depth env e fuel = .ok (v, remaining)) : PostHolds model post v := by
  have h := wp_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hwp henv hformula
  simpa only [he, Safe] using h

theorem wp_no_trap (hwp : wp e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    Program.eval fs depth env e fuel ≠ .error (.trap kind) := by
  intro he
  have h := wp_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hwp henv hformula
  simp only [he, Safe] at h

theorem wp_no_invalid (hwp : wp e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    Program.eval fs depth env e fuel ≠ .error .invalid := by
  intro he
  have h := wp_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hwp henv hformula
  simp only [he, Safe] at h

theorem wp_steps_value (hwp : wp e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model)
    (hs : Program.Steps fs (.eval e env []) (.ret v [])) : PostHolds model post v := by
  obtain ⟨depth, fuel, remaining, he⟩ := Program.eval_value_complete hs
  exact wp_value hwp henv hformula he

theorem wp_steps_no_trap (hwp : wp e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    ¬ Program.Steps fs (.eval e env []) (.trap kind) := by
  intro hs
  obtain ⟨depth, fuel, he⟩ := Program.eval_trap_complete hs
  exact wp_no_trap hwp henv hformula he

theorem wp_steps_no_invalid (hwp : wp e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    ¬ Program.Steps fs (.eval e env []) .invalid := by
  intro hs
  obtain ⟨depth, fuel, he⟩ := Program.eval_invalid_complete hs
  exact wp_no_invalid hwp henv hformula he

end APL.VCG
