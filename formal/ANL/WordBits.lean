import ANL.WordArithmetic

namespace ANL.Word

theorem complement_value_iff (a c : Word) :
    complement a = .value c ↔
      Valid a ∧ c.width = a.width ∧ c.value + a.value = a.width.modulus - 1 := by
  unfold complement
  by_cases h : Valid a
  · simp only [h, ite_true, true_and, Outcome.value.injEq]
    have hp := a.width.modulus_pos
    have ha : a.value < a.width.modulus := h
    constructor
    · intro hc; cases hc; exact ⟨rfl, by dsimp only; omega⟩
    · rintro ⟨hw, hc⟩
      cases c with
      | mk cw cn =>
        simp only at hw hc
        subst cw
        have : a.width.modulus - 1 - a.value = cn := by omega
        simp [this]
  · simp [h]

theorem complement_invalid_iff (a : Word) : complement a = .invalidInput ↔ ¬ Valid a := by
  unfold complement
  split <;> simp_all

@[simp] theorem complement_ne_trap (a : Word) (t : Trap) : complement a ≠ .trap t := by
  unfold complement
  split <;> simp

theorem complement_value_valid {a c : Word} (h : complement a = .value c) : Valid c := by
  obtain ⟨_, hw, hc⟩ := (complement_value_iff _ _).mp h
  have hp := a.width.modulus_pos
  unfold Valid
  rw [hw]
  omega

theorem complement_testBit {a c : Word} (h : complement a = .value c) (j : Nat) :
    c.value.testBit j = (decide (j < a.width.bits) && !a.value.testBit j) := by
  obtain ⟨ha, _, hc⟩ := (complement_value_iff _ _).mp h
  have he : c.value = 2 ^ a.width.bits - (a.value + 1) := by
    unfold Valid Width.modulus at ha
    unfold Width.modulus at hc
    omega
  rw [he]
  exact Nat.testBit_two_pow_sub_succ ha j

theorem complement_involution {a c : Word} (h : complement a = .value c) :
    complement c = .value a := by
  obtain ⟨_, hw, hc⟩ := (complement_value_iff _ _).mp h
  apply (complement_value_iff _ _).mpr
  exact ⟨complement_value_valid h, hw.symm, by rw [hw]; omega⟩

theorem binary_and_testBit {a b c : Word} (h : binary .bitAnd a b = .value c) (j : Nat) :
    c.value.testBit j = (a.value.testBit j && b.value.testBit j) := by
  have hc := ((binary_value_iff _ _ _ _).mp h).2.2.2
  change c.value = a.value &&& b.value at hc
  rw [hc, Nat.testBit_and]

theorem binary_or_testBit {a b c : Word} (h : binary .bitOr a b = .value c) (j : Nat) :
    c.value.testBit j = (a.value.testBit j || b.value.testBit j) := by
  have hc := ((binary_value_iff _ _ _ _).mp h).2.2.2
  change c.value = a.value ||| b.value at hc
  rw [hc, Nat.testBit_or]

theorem binary_xor_testBit {a b c : Word} (h : binary .bitXor a b = .value c) (j : Nat) :
    c.value.testBit j = (a.value.testBit j ^^ b.value.testBit j) := by
  have hc := ((binary_value_iff _ _ _ _).mp h).2.2.2
  change c.value = a.value ^^^ b.value at hc
  rw [hc, Nat.testBit_xor]

theorem ShiftCount_iff_toNat (w : Width) (i : Int) :
    ShiftCount w i ↔ 0 ≤ i ∧ i.toNat < w.bits := by unfold ShiftCount; omega

theorem ShiftCount_i64 (w : Width) (i : Int) (h : ShiftCount w i) : I64Range i := by
  have hw : w.bits ≤ 64 := by cases w <;> decide
  unfold ShiftCount at h
  unfold I64Range minI64 maxI64
  omega

/-- Logical shifts are multiplication modulo the width, or unsigned division by a power of two. -/
def ShiftPayload (op : ShiftOp) (w : Width) (a count c : Nat) : Prop :=
  match op with
  | .left => c = (a * 2 ^ count) % w.modulus
  | .right => c = a / 2 ^ count

def ShiftValue (op : ShiftOp) (a : Word) (i : Int) (c : Word) : Prop :=
  Valid a ∧ I64Range i ∧ ShiftCount a.width i ∧ c.width = a.width ∧
    ShiftPayload op a.width a.value i.toNat c.value

theorem shift_value_iff (op : ShiftOp) (a : Word) (i : Int) (c : Word) :
    shift op a i = .value c ↔ ShiftValue op a i c := by
  unfold shift ShiftValue
  by_cases hv : Valid a ∧ I64Range i
  · simp only [hv, ite_true, true_and]
    by_cases hc : ShiftCount a.width i
    · cases op <;> cases c <;> simp [hc, ShiftPayload, Word.mk.injEq, eq_comm]
    · simp [hc]
  · simp only [hv, ite_false, reduceCtorEq, false_iff]
    intro h
    exact hv ⟨h.1, h.2.1⟩

theorem shift_trap_iff (op : ShiftOp) (a : Word) (i : Int) (t : Trap) :
    shift op a i = .trap t ↔
      Valid a ∧ I64Range i ∧ t = .invalidShift ∧ (i < 0 ∨ (a.width.bits : Int) ≤ i) := by
  unfold shift
  by_cases hv : Valid a ∧ I64Range i
  · simp only [hv, ite_true, true_and]
    by_cases hc : ShiftCount a.width i
    · have hbounds := hc
      unfold ShiftCount at hbounds
      cases op <;> simp only [hc, ite_true, reduceCtorEq, false_iff] <;> omega
    · simp only [hc, ite_false, Outcome.trap.injEq]
      constructor
      · intro ht
        exact ⟨ht.symm, by unfold ShiftCount at hc; omega⟩
      · exact fun h => h.1.symm
  · simp only [hv, ite_false, reduceCtorEq, false_iff]
    intro h
    exact hv ⟨h.1, h.2.1⟩

theorem shift_invalid_iff (op : ShiftOp) (a : Word) (i : Int) :
    shift op a i = .invalidInput ↔ ¬ (Valid a ∧ I64Range i) := by
  unfold shift
  by_cases hv : Valid a ∧ I64Range i
  · by_cases hc : ShiftCount a.width i <;> cases op <;> simp [hv, hc]
  · simp [hv]

theorem shift_value_valid {op : ShiftOp} {a c : Word} {i : Int}
    (h : shift op a i = .value c) : Valid c := by
  obtain ⟨ha, _, _, hw, hc⟩ := (shift_value_iff _ _ _ _).mp h
  unfold Valid
  rw [hw]
  cases op with
  | left =>
    change c.value = _ at hc
    rw [hc]
    exact Nat.mod_lt _ a.width.modulus_pos
  | right =>
    change c.value = _ at hc
    rw [hc]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha

theorem shift_zero (op : ShiftOp) (a : Word) (h : Valid a) : shift op a 0 = .value a := by
  apply (shift_value_iff _ _ _ _).mpr
  refine ⟨h, by decide, ?_, rfl, ?_⟩
  · unfold ShiftCount
    have := a.width.bits_pos
    omega
  · cases op <;> simp [ShiftPayload, Nat.mod_eq_of_lt h]

/-- The independent mathematical result judgment is functional. -/
theorem BinaryValue_unique {op : BinaryOp} {a b c d : Word}
    (hc : BinaryValue op a b c) (hd : BinaryValue op a b d) : c = d := by
  have ec := (binary_value_iff _ _ _ _).mpr hc
  have ed := (binary_value_iff _ _ _ _).mpr hd
  exact Outcome.value.inj (ec.symm.trans ed)

theorem ShiftValue_unique {op : ShiftOp} {a c d : Word} {i : Int}
    (hc : ShiftValue op a i c) (hd : ShiftValue op a i d) : c = d := by
  have ec := (shift_value_iff _ _ _ _).mpr hc
  have ed := (shift_value_iff _ _ _ _).mpr hd
  exact Outcome.value.inj (ec.symm.trans ed)

end ANL.Word
