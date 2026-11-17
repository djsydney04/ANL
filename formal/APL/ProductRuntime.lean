import APL.ProductSupport
import APL.LoopVCGSoundness

namespace APL.ProductFlow
open ProductLogic
open ProductAnnotations
open VCG (MVal Model)

def runtimeLiteral : FlatProducts.Val → SymValue
  | .scalar value => .scalar (.literal (VCG.embed value))
  | .tuple fields => .tuple (fields.map fun value => .literal (VCG.embed value))

theorem runtime_literal_denotes : RuntimeDenotes model (runtimeLiteral value) value := by
  cases value with
  | scalar value => exact .scalar ⟨rfl, rfl⟩
  | tuple fields =>
    apply ProductDenotes.tuple
    change FieldsDenote model (fields.fields.map fun value => .literal (VCG.embed value))
      (fields.fields.map VCG.embed)
    induction fields.fields with
    | nil => exact .nil
    | cons value values ih => exact .cons ⟨rfl, rfl⟩ ih

theorem runtime_literal_supported : (runtimeLiteral value).Supported bound := by
  cases value with
  | scalar => trivial
  | tuple fields =>
    intro field member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    trivial

def machineUnaryGuard (op : UOp) (value : SymTerm) : Formula :=
  match op with
  | .neg => .range (.unary op value)
  | .not => .defined (.unary op value)

def machineDivisionGuard (left right : SymTerm) : Formula :=
  .and (.holds (.binary .ne right (.lit (.int 0))))
    (.not (.and (.holds (.binary .eq left (.lit (.int minI64))))
      (.holds (.binary .eq right (.lit (.int (-1)))))))

def machineBinaryGuard (op : BOp) (left right : SymTerm) : Formula :=
  match op with
  | .add | .sub | .mul => .range (.binary op left right)
  | .div | .rem => .and (machineDivisionGuard left right) (.range (.binary op left right))
  | _ => .defined (.binary op left right)

theorem unary_guard_value (ha : ScalarDenotes model symbol (VCG.embed value))
    (hg : (machineUnaryGuard op symbol.term).Holds model) :
    ∃ actual, FlatProducts.unary op (.scalar value) = .value actual ∧
      RuntimeDenotes model (.scalar (unaryScalar op symbol.term)) actual := by
  have oldGuard : (VCG.unaryGuard op (.lit (VCG.embed value))).Holds model := by
    cases op <;> simpa [machineUnaryGuard, VCG.unaryGuard, Formula.Holds, VCG.Formula.Holds,
      SymTerm.eval, VCG.SymTerm.eval, ha.2] using hg
  obtain ⟨actual, he, hd⟩ := LoopVCG.unary_guard_value
    (model := model) (symbol := .lit (VCG.embed value)) rfl oldGuard
  have hm : VCG.mUnary op (VCG.embed value) = some (VCG.embed actual) := by
    simpa [VCG.Denotes, VCG.SymTerm.eval] using hd
  refine ⟨.scalar actual, by simp [FlatProducts.unary, FlatProducts.embedResult, he], .scalar ?_⟩
  exact ⟨(math_unary_type hm).symm, by simp [unaryScalar, SymTerm.eval, ha.2, hm]⟩

theorem binary_guard_value (ha : ScalarDenotes model left (VCG.embed a))
    (hb : ScalarDenotes model right (VCG.embed b)) (hs : APL.shortCircuit op a = false)
    (hg : (machineBinaryGuard op left.term right.term).Holds model) :
    ∃ actual, FlatProducts.binary op (.scalar a) (.scalar b) = .value actual ∧
      RuntimeDenotes model (.scalar (binaryScalar op left.term right.term)) actual := by
  have oldGuard : (VCG.binaryGuard op (.lit (VCG.embed a)) (.lit (VCG.embed b))).Holds model := by
    cases op <;> simpa [machineBinaryGuard, machineDivisionGuard, VCG.binaryGuard, VCG.divisionGuard,
      Formula.Holds, VCG.Formula.Holds, SymTerm.eval, VCG.SymTerm.eval, ha.2, hb.2] using hg
  obtain ⟨actual, he, hd⟩ := LoopVCG.binary_guard_value (model := model)
    (left := .lit (VCG.embed a)) (right := .lit (VCG.embed b)) rfl rfl hs oldGuard
  have hmShort : VCG.mShort op (VCG.embed a) = false := by
    cases op <;> cases a <;> simp_all [VCG.mShort, VCG.embed, APL.shortCircuit]
    all_goals cases ‹Bool› <;> simp_all
  have hm : VCG.mBinary op (VCG.embed a) (VCG.embed b) = some (VCG.embed actual) := by
    simpa [VCG.Denotes, VCG.SymTerm.eval, hmShort] using hd
  refine ⟨.scalar actual, by simp [FlatProducts.binary, FlatProducts.embedResult, he], .scalar ?_⟩
  exact ⟨(math_binary_type hm).symm,
    by simp [binaryScalar, SymTerm.eval, ha.2, hb.2, hmShort, hm]⟩

def runtimeUnary (op : UOp) (value : SymValue) : Option Instantiated :=
  match value with
  | .scalar value =>
      if value.type = op.input then
        some ⟨.scalar (unaryScalar op value.term), machineUnaryGuard op value.term⟩
      else none
  | .tuple _ => none

def runtimeBinary (op : BOp) (left right : SymValue) : Option Instantiated := do
  let _ ← FlatProducts.binaryType op left.type right.type
  match left, right with
  | .scalar a, .scalar b =>
      return ⟨.scalar (binaryScalar op a.term b.term), machineBinaryGuard op a.term b.term⟩
  | .tuple a, .tuple b =>
      let term ← (if op = .ne then inequality (.tuple a) (.tuple b) else equality (.tuple a) (.tuple b))
      return ⟨.scalar (boolScalar term), equalityGuard left right⟩
  | _, _ => none

theorem runtime_unary_sound (hg : runtimeUnary op symbol = some output)
    (ha : RuntimeDenotes model symbol value) (hd : output.defined.Holds model) :
    ∃ actual, FlatProducts.unary op value = .value actual ∧ RuntimeDenotes model output.value actual := by
  cases symbol with
  | tuple fields => simp [runtimeUnary] at hg
  | scalar symbol =>
    simp only [runtimeUnary] at hg
    split at hg
    · cases hg
      cases value with
      | tuple fields => cases ha
      | scalar value => cases ha with | scalar ha => exact unary_guard_value ha hd
    · contradiction

theorem runtime_equality_instantiated (hop : op = .eq ∨ op = .ne) (ht : left.type = right.type)
    (hterm : (if op = .ne then inequality left right else equality left right) = some term)
    (hl : RuntimeDenotes model left a) (hr : RuntimeDenotes model right b) :
    ∃ value, FlatProducts.binary op a b = .value value ∧
      RuntimeDenotes model (.scalar (boolScalar term)) value := by
  have shape : a.type = b.type := by
    simpa using hl.shape.symm.trans (ht.trans hr.shape)
  rcases hop with rfl | rfl
  · obtain ⟨_, actual, hg, he⟩ := runtime_equality_sound hl hr ht
    change equality left right = some term at hterm
    rw [hg] at hterm
    cases hterm
    exact ⟨.scalar (.bool (decide (a = b))), flatProducts_equality shape, .scalar ⟨rfl, he⟩⟩
  · obtain ⟨_, actual, hg, he⟩ := runtime_inequality_sound hl hr ht
    change inequality left right = some term at hterm
    rw [hg] at hterm
    cases hterm
    exact ⟨.scalar (.bool (decide (a ≠ b))), flatProducts_inequality shape, .scalar ⟨rfl, he⟩⟩

theorem runtime_binary_sound (hg : runtimeBinary op left right = some output)
    (hl : RuntimeDenotes model left a) (hr : RuntimeDenotes model right b)
    (hs : FlatProducts.shortCircuit op a = false) (hd : output.defined.Holds model) :
    ∃ actual, FlatProducts.binary op a b = .value actual ∧ RuntimeDenotes model output.value actual := by
  cases left with
  | scalar left =>
    cases right with
    | scalar right =>
      simp only [runtimeBinary, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
      obtain ⟨type, _, heq⟩ := hg
      cases heq
      cases a with
      | tuple fields => cases hl
      | scalar a =>
        cases b with
        | tuple fields => cases hr
        | scalar b =>
          cases hl with
          | scalar hl => cases hr with | scalar hr => exact binary_guard_value hl hr hs hd
    | tuple right => simp [runtimeBinary, SymValue.type, FlatProducts.binaryType] at hg
  | tuple left =>
    cases right with
    | scalar right => simp [runtimeBinary, SymValue.type, FlatProducts.binaryType] at hg
    | tuple right =>
      simp only [runtimeBinary, SymValue.type, FlatProducts.binaryType] at hg
      split at hg
      next ht =>
        simp only [bind, Option.bind_some, Option.bind_eq_some_iff, Option.pure_def] at hg
        obtain ⟨term, hterm, heq⟩ := hg
        cases heq
        exact runtime_equality_instantiated (left := .tuple left) (right := .tuple right) ht.1 (congrArg FlatProducts.Ty.tuple ht.2) hterm hl hr
      · simp at hg

end APL.ProductFlow
