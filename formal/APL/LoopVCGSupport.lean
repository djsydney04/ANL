import APL.StateVCGContracts
import APL.LocalStateFrame

namespace APL.LoopVCG
open VCG

def Below (bound : Nat) : SymTerm → Prop
  | .lit _ => True
  | .var i => i < bound
  | .unary _ a => Below bound a
  | .binary _ a b => Below bound a ∧ Below bound b

def SymbolsBelow (bound : Nat) : List SymTerm → Prop
  | [] => True
  | a :: rest => Below bound a ∧ SymbolsBelow bound rest

def AgreeBelow (bound : Nat) (a b : Model) : Prop := ∀ i, i < bound → a i = b i

theorem eval_agree (hs : Below bound s) (ha : AgreeBelow bound a b) : s.eval a = s.eval b := by
  induction s with
  | lit _ => rfl
  | var i => exact congrArg some (ha i hs)
  | unary op s ih => simp only [SymTerm.eval, ih hs]
  | binary op s t ihs iht => simp only [SymTerm.eval, ihs hs.1, iht hs.2]

theorem below_mono (h : Below n s) (hn : n ≤ m) : Below m s := by
  induction s with
  | lit _ => trivial
  | var i => exact Nat.lt_of_lt_of_le h hn
  | unary op s ih => exact ih h
  | binary op s t ihs iht => exact ⟨ihs h.1, iht h.2⟩

theorem symbols_below_mono (h : SymbolsBelow n syms) (hn : n ≤ m) : SymbolsBelow m syms := by
  induction syms with
  | nil => trivial
  | cons s ss ih => exact ⟨below_mono h.1 hn, ih h.2⟩

theorem denotes_agree (hs : Below bound s) (ha : AgreeBelow bound a b) (hd : Denotes a s v) :
    Denotes b s v := (eval_agree hs ha).symm.trans hd

theorem env_agree (hs : SymbolsBelow bound syms) (ha : AgreeBelow bound a b)
    (he : EnvRep a syms env) : EnvRep b syms env := by
  induction he with
  | nil => exact .nil
  | cons hd _ ih => exact .cons (denotes_agree hs.1 ha hd) (ih hs.2)

def FormulaBelow (bound : Nat) : Formula → Prop
  | .truth _ => True
  | .holds s | .defined s | .boolean s | .range s => Below bound s
  | .and a b | .imp a b => FormulaBelow bound a ∧ FormulaBelow bound b
  | .not a => FormulaBelow bound a

theorem formula_agree (hs : FormulaBelow bound f) (ha : AgreeBelow bound a b) :
    f.Holds a ↔ f.Holds b := by
  induction f with
  | truth _ => rfl
  | holds s => simp only [Formula.Holds, eval_agree hs ha]
  | defined s => simp only [Formula.Holds, eval_agree hs ha]
  | boolean s => simp only [Formula.Holds, eval_agree hs ha]
  | range s => simp only [Formula.Holds, eval_agree hs ha]
  | and f g ihf ihg => simp only [Formula.Holds, ihf hs.1, ihg hs.2]
  | imp f g ihf ihg => simp only [Formula.Holds, ihf hs.1, ihg hs.2]
  | not f ih => simp only [Formula.Holds, ih hs]

def overwrite (model : Model) (index : Nat) (value : MVal) : Model :=
  fun i => if i = index then value else model i

theorem overwrite_agrees : AgreeBelow n model (overwrite model n value) := by
  intro i hi
  simp [overwrite, Nat.ne_of_lt hi]

/-- Retain immutable cells and freshen every mutable nonunit cell. Mutable unit
cells use a literal and consume no identity; coverage therefore requires typing. -/
def freshEnv : LocalState.Ctx → List SymTerm → Nat → Option (List SymTerm × Nat)
  | [], [], next => some ([], next)
  | (_, false) :: Γ, s :: ss, next => do
      let (tail, final) ← freshEnv Γ ss next
      return (s :: tail, final)
  | (.unit, true) :: Γ, _ :: ss, next => do
      let (tail, final) ← freshEnv Γ ss next
      return (.lit .unit :: tail, final)
  | (_, true) :: Γ, _ :: ss, next => do
      let (tail, final) ← freshEnv Γ ss (next + 1)
      return (.var next :: tail, final)
  | _, _, _ => none

theorem fresh_covers (hgen : freshEnv Γ syms next = some (head, final))
    (hs : SymbolsBelow next syms) (he : EnvRep model syms entry)
    (hfrozen : LocalState.Frozen Γ entry actual) (htyped : LocalState.EnvTyped actual Γ) :
    ∃ extended, AgreeBelow next model extended ∧ EnvRep extended head actual := by
  induction hfrozen generalizing syms next head final model with
  | nil =>
    cases he
    cases hgen
    exact ⟨model, fun _ _ => rfl, .nil⟩
  | @cons permission a b Γ as bs t hsame _ ih =>
    cases he with
    | @cons s v ss vs hd htail =>
      cases permission with
      | false =>
        simp only [freshEnv, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
        obtain ⟨⟨tail, finish⟩, hg, heq⟩ := hgen
        cases heq
        obtain ⟨extended, ha, hr⟩ := ih hg hs.2 htail (LocalState.env_tail htyped)
        have eq := hsame rfl
        subst b
        exact ⟨extended, ha, .cons (denotes_agree hs.1 ha hd) hr⟩
      | true =>
        cases t with
        | unit =>
          simp only [freshEnv, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
          obtain ⟨⟨tail, finish⟩, hg, heq⟩ := hgen
          cases heq
          obtain ⟨extended, ha, hr⟩ := ih hg hs.2 htail (LocalState.env_tail htyped)
          have hb : b.type = .unit := (List.cons.inj htyped).1
          cases b with
          | int _ | bool _ => simp [Val.type] at hb
          | unit => exact ⟨extended, ha, .cons rfl hr⟩
        | i64 | bool =>
          simp only [freshEnv, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
          obtain ⟨⟨tail, finish⟩, hg, heq⟩ := hgen
          cases heq
          let updated := overwrite model next (VCG.embed b)
          have hm : AgreeBelow next model updated := overwrite_agrees
          have htail' := env_agree hs.2 hm htail
          obtain ⟨extended, ha, hr⟩ := ih hg (symbols_below_mono hs.2 (Nat.le_succ next)) htail'
            (LocalState.env_tail htyped)
          refine ⟨extended, ?_, .cons ?_ hr⟩
          · intro i hi
            exact (hm i hi).trans (ha i (Nat.lt_trans hi (Nat.lt_succ_self next)))
          · change some (extended next) = some (VCG.embed b)
            rw [← ha next (Nat.lt_succ_self next)]
            simp [updated, overwrite]

theorem fresh_bounded (hgen : freshEnv Γ syms next = some (head, final))
    (hs : SymbolsBelow next syms) : next ≤ final ∧ SymbolsBelow final head := by
  induction Γ generalizing syms next head final with
  | nil =>
    cases syms with
    | nil => cases hgen; exact ⟨Nat.le_refl _, trivial⟩
    | cons _ _ => simp [freshEnv] at hgen
  | cons binding Γ ih =>
    cases syms with
    | nil => simp [freshEnv] at hgen
    | cons s ss =>
      obtain ⟨t, permission⟩ := binding
      cases permission with
      | false =>
        simp only [freshEnv, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
        obtain ⟨⟨tail, finish⟩, hg, heq⟩ := hgen
        cases heq
        obtain ⟨hn, ht⟩ := ih hg hs.2
        exact ⟨hn, below_mono hs.1 hn, ht⟩
      | true =>
        cases t with
        | unit =>
          simp only [freshEnv, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
          obtain ⟨⟨tail, finish⟩, hg, heq⟩ := hgen
          cases heq
          obtain ⟨hn, ht⟩ := ih hg hs.2
          exact ⟨hn, trivial, ht⟩
        | i64 | bool =>
          simp only [freshEnv, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
          obtain ⟨⟨tail, finish⟩, hg, heq⟩ := hgen
          cases heq
          obtain ⟨hn, ht⟩ := ih hg (symbols_below_mono hs.2 (Nat.le_succ next))
          exact ⟨Nat.le_trans (Nat.le_succ next) hn, Nat.lt_of_lt_of_le (Nat.lt_succ_self next) hn, ht⟩

def freshCount : LocalState.Ctx → Nat
  | [] => 0
  | (_, false) :: Γ | (.unit, true) :: Γ => freshCount Γ
  | (_, true) :: Γ => freshCount Γ + 1

def headIds : LocalState.Ctx → List SymTerm → Option (List Nat)
  | [], [] => some []
  | (_, false) :: Γ, _ :: ss | (.unit, true) :: Γ, _ :: ss => headIds Γ ss
  | (_, true) :: Γ, .var i :: ss => (headIds Γ ss).map (i :: ·)
  | _, _ => none

theorem fresh_shape (hgen : freshEnv Γ syms next = some (head, final)) :
    final = next + freshCount Γ ∧ headIds Γ head = some (List.range' next (freshCount Γ)) := by
  induction Γ generalizing syms next head final with
  | nil =>
    cases syms with
    | nil => cases hgen; exact ⟨by simp [freshCount], rfl⟩
    | cons _ _ => simp [freshEnv] at hgen
  | cons binding Γ ih =>
    cases syms with
    | nil => simp [freshEnv] at hgen
    | cons s ss =>
      obtain ⟨ty, permission⟩ := binding
      cases permission <;> cases ty <;>
        simp only [freshEnv, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
      all_goals
        obtain ⟨⟨tail, finish⟩, hg, heq⟩ := hgen
        cases heq
        obtain ⟨hcount, hids⟩ := ih hg
        constructor
        · simp only [freshCount] at hcount ⊢; omega
        · simp [headIds, freshCount, hids, List.range'_succ]

theorem fresh_distinct (hgen : freshEnv Γ syms next = some (head, final)) :
    ∃ ids, headIds Γ head = some ids ∧ ids.Nodup ∧
      ∀ i ∈ ids, next ≤ i ∧ i < final := by
  obtain ⟨hcount, hids⟩ := fresh_shape hgen
  refine ⟨List.range' next (freshCount Γ), hids, List.nodup_range', ?_⟩
  intro i hi
  rw [List.mem_range'_1] at hi
  exact ⟨hi.1, hcount ▸ hi.2⟩

theorem fresh_disjoint
    (ha : freshEnv Γa symsA start = some (headA, middle))
    (hb : freshEnv Γb symsB middle = some (headB, finish))
    (hia : headIds Γa headA = some idsA) (hib : headIds Γb headB = some idsB) :
    ∀ i ∈ idsA, i ∉ idsB := by
  obtain ⟨_, hcountA, _, hboundA⟩ := fresh_distinct ha
  obtain ⟨_, hcountB, _, hboundB⟩ := fresh_distinct hb
  rw [hia] at hcountA
  rw [hib] at hcountB
  cases hcountA
  cases hcountB
  intro i hai hbi
  have a := hboundA i hai
  have b := hboundB i hbi
  omega

structure Check where
  guard : Formula
  required : Formula

def group (checks : List Check) : Formula :=
  checks.foldr (fun check rest => .and (.imp check.guard check.required) rest) (.truth true)

/-- Conjunction preserves every recorded guarded check. This does not establish
that a generator or a named-query partition recorded all required checks. -/
theorem group_exact : (group checks).Holds model ↔
    ∀ check ∈ checks, check.guard.Holds model → check.required.Holds model := by
  induction checks with
  | nil => simp [group, Formula.Holds]
  | cons check rest ih =>
    change ((check.guard.Holds model → check.required.Holds model) ∧ (group rest).Holds model) ↔ _
    rw [ih]
    simp

def typeGuard (ty : Ty) (s : SymTerm) : Formula :=
  match ty with
  | .i64 => .range s
  | .bool => .boolean s
  | .unit => .holds (.binary .eq s (.lit .unit))

theorem represented_type (ht : v.type = ty) (hd : Denotes model s v) :
    (typeGuard ty s).Holds model := by
  cases v with
  | int n =>
    subst ty
    exact ⟨n.val, hd, n.property⟩
  | bool b =>
    subst ty
    exact ⟨b, hd⟩
  | unit =>
    subst ty
    unfold Denotes at hd
    simp [typeGuard, Val.type, Formula.Holds, SymTerm.eval, hd, mShort, mBinary, MVal.type, VCG.embed]

def headDomain : LocalState.Ctx → List SymTerm → Option Formula
  | [], [] => some (.truth true)
  | (ty, _) :: Γ, symbol :: rest => do
      let tail ← headDomain Γ rest
      return .and (typeGuard ty symbol) tail
  | _, _ => none

theorem head_domain_sound (hgen : headDomain Γ syms = some formula)
    (he : EnvRep model syms env) (ht : LocalState.EnvTyped env Γ) : formula.Holds model := by
  induction he generalizing Γ formula with
  | nil =>
    cases Γ with
    | nil => cases hgen; rfl
    | cons _ _ => simp [LocalState.EnvTyped] at ht
  | cons hd _ ih =>
    cases Γ with
    | nil => simp [LocalState.EnvTyped] at ht
    | cons binding Γ =>
      obtain ⟨ty, permission⟩ := binding
      simp only [headDomain, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
      obtain ⟨tail, hg, heq⟩ := hgen
      cases heq
      exact ⟨represented_type (List.cons.inj ht).1 hd, ih hg (LocalState.env_tail ht)⟩

structure Head where
  symbols : List SymTerm
  domain : Formula
  next : Nat

def freshHead (Γ : LocalState.Ctx) (syms : List SymTerm) (next : Nat) : Option Head := do
  let (symbols, final) ← freshEnv Γ syms next
  let domain ← headDomain Γ symbols
  return ⟨symbols, domain, final⟩

/-- Every typed concrete head preserving immutable cells has a fresh model witness. -/
theorem fresh_head_coverage (hgen : freshHead Γ syms next = some head)
    (hs : SymbolsBelow next syms) (he : EnvRep model syms entry)
    (hfrozen : LocalState.Frozen Γ entry actual) (htyped : LocalState.EnvTyped actual Γ) :
    next ≤ head.next ∧ SymbolsBelow head.next head.symbols ∧
      ∃ extended, AgreeBelow next model extended ∧ EnvRep extended head.symbols actual ∧
        head.domain.Holds extended := by
  simp only [freshHead, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨symbols, final⟩, hfresh, domain, hdomain, heq⟩ := hgen
  cases heq
  obtain ⟨hn, hb⟩ := fresh_bounded hfresh hs
  obtain ⟨extended, ha, hrep⟩ := fresh_covers hfresh hs he hfrozen htyped
  exact ⟨hn, hb, extended, ha, hrep, head_domain_sound hdomain hrep htyped⟩

example : freshEnv [(.i64, false), (.unit, true), (.bool, true), (.i64, true)]
    [.var 0, .lit .unit, .lit (.bool true), .lit (.int 1)] 5 =
    some ([.var 0, .lit .unit, .var 5, .var 6], 7) := by rfl

example : freshEnv [(.unit, true)] [.lit .unit] 5 = some ([.lit .unit], 5) := by rfl

example : freshEnv [(.i64, true)] [] 0 = none := by rfl

end APL.LoopVCG
