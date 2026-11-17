import APL.LoopGenerationSupport

/-! Explicit syntax sizes and a supplied natural rank covering every syntactic
call. These definitions do not establish rank existence or source graph extraction. -/

namespace APL.LoopGeneration
open VCG LoopVCG LoopAnnotations

mutual
  def nodes : Term → Nat
    | .lit _ | .local _ => 1
    | .letE a b | .letMut a b | .binary _ a b => 1 + nodes a + nodes b
    | .assign _ a | .unary _ a => 1 + nodes a
    | .ifE c a b => 1 + nodes c + nodes a + nodes b
    | .whileE _ c b => 1 + nodes c + nodes b
    | .call _ args => 1 + argumentNodes args
  def argumentNodes : List Term → Nat
    | [] => 0
    | a :: rest => nodes a + argumentNodes rest
end

mutual
  /-- Covers all syntax, including dead branches, loop children and call arguments. -/
  def CallsBelow (rank : Nat → Nat) (ceiling : Nat) : Term → Prop
    | .lit _ | .local _ => True
    | .letE a b | .letMut a b | .binary _ a b => CallsBelow rank ceiling a ∧ CallsBelow rank ceiling b
    | .assign _ a | .unary _ a => CallsBelow rank ceiling a
    | .ifE c a b => CallsBelow rank ceiling c ∧ CallsBelow rank ceiling a ∧ CallsBelow rank ceiling b
    | .whileE _ c b => CallsBelow rank ceiling c ∧ CallsBelow rank ceiling b
    | .call f args => rank f < ceiling ∧ ArgumentsBelow rank ceiling args
  def ArgumentsBelow (rank : Nat → Nat) (ceiling : Nat) : List Term → Prop
    | [] => True
    | a :: rest => CallsBelow rank ceiling a ∧ ArgumentsBelow rank ceiling rest
end

def Ranked (fs : Functions) (rank : Nat → Nat) : Prop :=
  ∀ f fn, fs[f]? = some fn → CallsBelow rank (rank f) fn.body

def bodyBound (fs : Functions) : Nat :=
  1 + (fs.toList.map fun fn => nodes fn.body).sum

theorem member_sum_bound {xs : List Nat} (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => cases h
  | cons a rest ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · simp [List.sum_cons]
    · have := ih ht
      simp only [List.sum_cons]
      omega

theorem body_bounded {fs : Functions} {f : Nat} {fn : Function} (h : fs[f]? = some fn) : nodes fn.body < bodyBound fs := by
  have member : fn ∈ fs.toList := by
    simpa using Array.mem_of_getElem? h
  have hn := member_sum_bound (xs := fs.toList.map (fun fn => nodes fn.body)) (List.mem_map.mpr ⟨fn, member, rfl⟩)
  unfold bodyBound
  omega

theorem nodes_positive (e : Term) : 0 < nodes e := by
  cases e <;> simp only [nodes] <;> omega

theorem argument_node_bound (h : a ∈ args) : nodes a ≤ argumentNodes args := by
  induction args with
  | nil => cases h
  | cons x rest ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · simp only [argumentNodes]; omega
    · have := ih ht
      simp only [argumentNodes]
      omega

theorem arguments_rank (h : ArgumentsBelow rank ceiling args) (hm : a ∈ args) :
    CallsBelow rank ceiling a := by
  induction args with
  | nil => cases hm
  | cons x rest ih =>
    rcases List.mem_cons.mp hm with rfl | ht
    · exact h.1
    · exact ih h.2 ht

theorem rank_cost_decreases {rank : Nat → Nat} (hr : rank f < ceiling) (hf : fs[f]? = some fn) :
    rank f * bodyBound fs + nodes fn.body < ceiling * bodyBound fs + nodes (.call f args) := by
  have hb := body_bounded hf
  have hc : (rank f + 1) * bodyBound fs ≤ ceiling * bodyBound fs :=
    Nat.mul_le_mul_right _ hr
  rw [Nat.add_mul] at hc
  simp only [Nat.one_mul] at hc
  omega

end APL.LoopGeneration
