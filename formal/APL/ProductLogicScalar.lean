import APL.VCG

namespace APL.ProductLogic

open VCG (MVal Model mUnary mBinary mShort)

inductive SymTerm where
  | lit (value : MVal)
  | var (index : Nat)
  | unary (op : UOp) (a : SymTerm)
  | binary (op : BOp) (a b : SymTerm)
  | ite (condition yes no : SymTerm)
  deriving Repr, DecidableEq

def SymTerm.eval (model : Model) : SymTerm → Option MVal
  | .lit v => some v
  | .var i => some (model i)
  | .unary op a => do mUnary op (← a.eval model)
  | .binary op a b => do
      let va ← a.eval model
      if mShort op va then some va else mBinary op va (← b.eval model)
  | .ite condition yes no => do
      match ← condition.eval model with
      | .bool true => yes.eval model
      | .bool false => no.eval model
      | _ => none

def embedTerm : VCG.SymTerm → SymTerm
  | .lit v => .lit v
  | .var i => .var i
  | .unary op a => .unary op (embedTerm a)
  | .binary op a b => .binary op (embedTerm a) (embedTerm b)

@[simp] theorem embedTerm_eval (term : VCG.SymTerm) (model : Model) :
    (embedTerm term).eval model = term.eval model := by
  induction term <;> simp_all [embedTerm, SymTerm.eval, VCG.SymTerm.eval]

@[simp] theorem eval_ite_true (hc : condition.eval model = some (.bool true)) :
    (SymTerm.ite condition yes no).eval model = yes.eval model := by
  simp [SymTerm.eval, hc]

@[simp] theorem eval_ite_false (hc : condition.eval model = some (.bool false)) :
    (SymTerm.ite condition yes no).eval model = no.eval model := by
  simp [SymTerm.eval, hc]

theorem eval_ite_selected (hc : condition.eval model = some (.bool b)) :
    (SymTerm.ite condition yes no).eval model = (if b then yes else no).eval model := by
  cases b <;> simp_all

inductive Formula where
  | truth (b : Bool)
  | holds (term : SymTerm)
  | defined (term : SymTerm)
  | boolean (term : SymTerm)
  | range (term : SymTerm)
  | and (a b : Formula)
  | not (a : Formula)
  | imp (a b : Formula)
  deriving Repr

def Formula.Holds (model : Model) : Formula → Prop
  | .truth b => b = true
  | .holds term => term.eval model = some (.bool true)
  | .defined term => ∃ v, term.eval model = some v
  | .boolean term => ∃ b, term.eval model = some (.bool b)
  | .range term => ∃ n, term.eval model = some (.int n) ∧ InRange n
  | .and a b => a.Holds model ∧ b.Holds model
  | .not a => ¬ a.Holds model
  | .imp a b => a.Holds model → b.Holds model

def embedFormula : VCG.Formula → Formula
  | .truth b => .truth b
  | .holds term => .holds (embedTerm term)
  | .defined term => .defined (embedTerm term)
  | .boolean term => .boolean (embedTerm term)
  | .range term => .range (embedTerm term)
  | .and a b => .and (embedFormula a) (embedFormula b)
  | .not a => .not (embedFormula a)
  | .imp a b => .imp (embedFormula a) (embedFormula b)

@[simp] theorem embedFormula_holds (formula : VCG.Formula) (model : Model) :
    (embedFormula formula).Holds model ↔ formula.Holds model := by
  induction formula <;> simp_all [embedFormula, Formula.Holds, VCG.Formula.Holds]

theorem embed_denotes (term : VCG.SymTerm) (value : APL.Val) (model : Model) :
    (embedTerm term).eval model = some (VCG.embed value) ↔ VCG.Denotes model term value := by
  simp [VCG.Denotes]

def SymTerm.Supported (bound : Nat) : SymTerm → Prop
  | .lit _ => True
  | .var index => index < bound
  | .unary _ a => a.Supported bound
  | .binary _ a b => a.Supported bound ∧ b.Supported bound
  | .ite c a b => c.Supported bound ∧ a.Supported bound ∧ b.Supported bound

def AgreeBelow (bound : Nat) (left right : Model) : Prop :=
  ∀ index, index < bound → left index = right index

theorem SymTerm.eval_agree (term : SymTerm) (hs : term.Supported bound)
    (ha : AgreeBelow bound left right) : term.eval left = term.eval right := by
  induction term with
  | lit => rfl
  | var index => exact congrArg some (ha index hs)
  | unary op a ih => simp only [SymTerm.eval, ih hs]
  | binary op a b iha ihb => simp only [SymTerm.eval, iha hs.1, ihb hs.2]
  | ite c a b ihc iha ihb =>
      simp only [SymTerm.eval, ihc hs.1, iha hs.2.1, ihb hs.2.2]

theorem SymTerm.supported_mono (term : SymTerm) (hs : term.Supported bound)
    (hle : bound ≤ larger) : term.Supported larger := by
  induction term with
  | lit => trivial
  | var index => exact Nat.lt_of_lt_of_le hs hle
  | unary op a ih => exact ih hs
  | binary op a b iha ihb => exact ⟨iha hs.1, ihb hs.2⟩
  | ite c a b ihc iha ihb => exact ⟨ihc hs.1, iha hs.2.1, ihb hs.2.2⟩

def Formula.Supported (bound : Nat) : Formula → Prop
  | .truth _ => True
  | .holds term | .defined term | .boolean term | .range term => term.Supported bound
  | .and a b | .imp a b => a.Supported bound ∧ b.Supported bound
  | .not a => a.Supported bound

theorem Formula.holds_agree (formula : Formula) (hs : formula.Supported bound)
    (ha : AgreeBelow bound left right) : formula.Holds left ↔ formula.Holds right := by
  induction formula with
  | truth => rfl
  | holds term | defined term | boolean term | range term =>
      simp only [Formula.Holds, term.eval_agree hs ha]
  | and a b iha ihb | imp a b iha ihb =>
      simp only [Formula.Holds, iha hs.1, ihb hs.2]
  | not a ih => simp only [Formula.Holds, ih hs]

end APL.ProductLogic
