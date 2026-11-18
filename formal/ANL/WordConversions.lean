import ANL.WordArithmetic

namespace ANL.Word

/-- Literal acceptance includes the raw width and exact payload, not just a range check. -/
theorem decodeLiteral_iff (width value : Nat) (c : Word) :
    decodeLiteral width value = some c ↔
      width = c.width.bits ∧ value = c.value ∧ Valid c := by
  change (Width.decode width).bind (fun w => if value < w.modulus then some ⟨w, value⟩ else none) = some c ↔ _
  simp only [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨w, hw, h⟩
    split at h
    next hv =>
      cases h
      exact ⟨(Width.decode_iff _ _).mp hw, rfl, hv⟩
    next => cases h
  · rintro ⟨hw, hv, h⟩
    refine ⟨c.width, (Width.decode_iff _ _).mpr hw, ?_⟩
    subst value
    cases c
    unfold Valid at h
    simp only [h, ite_true]

theorem decodeLiteral_valid {width value : Nat} {c : Word}
    (h : decodeLiteral width value = some c) : Valid c :=
  ((decodeLiteral_iff _ _ _).mp h).2.2

theorem decodeLiteral_u64_bound {width value : Nat} {c : Word}
    (h : decodeLiteral width value = some c) : value ≤ 18446744073709551615 := by
  obtain ⟨_, rfl, hv⟩ := (decodeLiteral_iff _ _ _).mp h
  exact valid_u64_bound hv

theorem checkedFromI64_value_iff (w : Width) (i : Int) (c : Word) :
    checkedFromI64 w i = .value c ↔
      I64Range i ∧ c.width = w ∧ Valid c ∧ (c.value : Int) = i := by
  unfold checkedFromI64
  by_cases h : I64Range i <;> simp [h, checkedInteger_value_iff]

theorem checkedFromI64_trap_iff (w : Width) (i : Int) (t : Trap) :
    checkedFromI64 w i = .trap t ↔
      I64Range i ∧ t = .overflow ∧ (i < 0 ∨ (w.modulus : Int) ≤ i) := by
  unfold checkedFromI64
  by_cases h : I64Range i
  · simp only [h, ite_true, true_and, checkedInteger_trap_iff]
    constructor <;> rintro ⟨ht, hi⟩ <;> exact ⟨ht, by omega⟩
  · simp [h]

theorem checkedFromI64_invalid_iff (w : Width) (i : Int) :
    checkedFromI64 w i = .invalidInput ↔ ¬ I64Range i := by
  unfold checkedFromI64
  split <;> simp_all

theorem truncateFromI64_value_iff (w : Width) (i : Int) (c : Word) :
    truncateFromI64 w i = .value c ↔
      I64Range i ∧ c.width = w ∧ Valid c ∧ (c.value : Int) = i % (w.modulus : Int) := by
  unfold truncateFromI64
  by_cases h : I64Range i
  · simp only [h, ite_true, true_and]
    exact modulo_value_iff _ _ _
  · simp [h]

theorem truncateFromI64_invalid_iff (w : Width) (i : Int) :
    truncateFromI64 w i = .invalidInput ↔ ¬ I64Range i := by
  unfold truncateFromI64
  split <;> simp_all

@[simp] theorem truncateFromI64_ne_trap (w : Width) (i : Int) (t : Trap) :
    truncateFromI64 w i ≠ .trap t := by unfold truncateFromI64; split <;> simp

theorem checkedToI64_value_iff (a : Word) (i : Int) :
    checkedToI64 a = .value i ↔ Valid a ∧ i = (a.value : Int) ∧ I64Range i := by
  unfold checkedToI64
  by_cases hv : Valid a
  · simp only [hv, ite_true, true_and]
    by_cases hr : (a.value : Int) ≤ maxI64
    · simp only [hr, ite_true, Outcome.value.injEq]
      constructor
      · intro hi; subst i
        exact ⟨rfl, by unfold I64Range minI64; omega⟩
      · exact fun h => h.1.symm
    · simp only [hr, ite_false, reduceCtorEq, false_iff]
      rintro ⟨rfl, h⟩
      exact hr h.2
  · simp [hv]

theorem checkedToI64_trap_iff (a : Word) (t : Trap) :
    checkedToI64 a = .trap t ↔ Valid a ∧ t = .overflow ∧ maxI64 < (a.value : Int) := by
  unfold checkedToI64
  by_cases hv : Valid a
  · simp only [hv, ite_true, true_and]
    by_cases hr : (a.value : Int) ≤ maxI64 <;> simp [hr, eq_comm]
    omega
  · simp [hv]

theorem checkedToI64_invalid_iff (a : Word) :
    checkedToI64 a = .invalidInput ↔ ¬ Valid a := by
  unfold checkedToI64
  split
  · split <;> simp_all
  · simp_all

theorem checkedToI64_value_range {a : Word} {i : Int}
    (h : checkedToI64 a = .value i) : I64Range i :=
  ((checkedToI64_value_iff _ _).mp h).2.2

theorem checkedWordCast_value_iff (w : Width) (a c : Word) :
    checkedWordCast w a = .value c ↔ Valid a ∧ c.width = w ∧ Valid c ∧ c.value = a.value := by
  unfold checkedWordCast
  by_cases h : Valid a
  · simp only [h, ite_true, true_and, checkedInteger_value_iff]
    constructor <;> rintro ⟨hw, hc, hv⟩ <;> exact ⟨hw, hc, by omega⟩
  · simp [h]

theorem checkedWordCast_trap_iff (w : Width) (a : Word) (t : Trap) :
    checkedWordCast w a = .trap t ↔ Valid a ∧ t = .overflow ∧ w.modulus ≤ a.value := by
  unfold checkedWordCast
  by_cases h : Valid a
  · simp only [h, ite_true, true_and, checkedInteger_trap_iff]
    constructor <;> rintro ⟨ht, ha⟩ <;> exact ⟨ht, by omega⟩
  · simp [h]

theorem checkedWordCast_invalid_iff (w : Width) (a : Word) :
    checkedWordCast w a = .invalidInput ↔ ¬ Valid a := by
  unfold checkedWordCast
  split <;> simp_all

theorem truncateWordCast_value_iff (w : Width) (a c : Word) :
    truncateWordCast w a = .value c ↔
      Valid a ∧ c.width = w ∧ c.value = a.value % w.modulus := by
  unfold truncateWordCast
  by_cases h : Valid a
  · cases c
    simp [h, Word.mk.injEq, eq_comm]
  · simp [h]

theorem truncateWordCast_invalid_iff (w : Width) (a : Word) :
    truncateWordCast w a = .invalidInput ↔ ¬ Valid a := by
  unfold truncateWordCast
  split <;> simp_all

@[simp] theorem truncateWordCast_ne_trap (w : Width) (a : Word) (t : Trap) :
    truncateWordCast w a ≠ .trap t := by unfold truncateWordCast; split <;> simp

theorem checkedFromI64_value_valid {w : Width} {i : Int} {c : Word}
    (h : checkedFromI64 w i = .value c) : Valid c :=
  ((checkedFromI64_value_iff _ _ _).mp h).2.2.1

theorem truncateFromI64_value_valid {w : Width} {i : Int} {c : Word}
    (h : truncateFromI64 w i = .value c) : Valid c :=
  ((truncateFromI64_value_iff _ _ _).mp h).2.2.1

theorem checkedWordCast_value_valid {w : Width} {a c : Word}
    (h : checkedWordCast w a = .value c) : Valid c :=
  ((checkedWordCast_value_iff _ _ _).mp h).2.2.1

theorem truncateWordCast_value_valid {w : Width} {a c : Word}
    (h : truncateWordCast w a = .value c) : Valid c := by
  obtain ⟨_, hw, hv⟩ := (truncateWordCast_value_iff _ _ _).mp h
  unfold Valid
  rw [hw, hv]
  exact Nat.mod_lt _ w.modulus_pos

/-- An unsigned identity cast succeeds throughout the full width, including u64 above maxI64. -/
theorem checkedWordCast_self (a : Word) (h : Valid a) :
    checkedWordCast a.width a = .value a := by
  exact (checkedWordCast_value_iff _ _ _).mpr ⟨h, rfl, h, rfl⟩

theorem truncateWordCast_self (a : Word) (h : Valid a) :
    truncateWordCast a.width a = .value a := by
  exact (truncateWordCast_value_iff _ _ _).mpr ⟨h, rfl, (Nat.mod_eq_of_lt h).symm⟩

theorem checkedCast_then_truncate {w : Width} {a c : Word}
    (h : checkedWordCast w a = .value c) : truncateWordCast w a = .value c := by
  obtain ⟨ha, hw, hc, hv⟩ := (checkedWordCast_value_iff _ _ _).mp h
  apply (truncateWordCast_value_iff _ _ _).mpr
  refine ⟨ha, hw, ?_⟩
  unfold Valid at hc
  rw [hw, hv] at hc
  rw [hv, Nat.mod_eq_of_lt hc]

theorem checked_i64_roundtrip {w : Width} {i : Int} {c : Word}
    (h : checkedFromI64 w i = .value c) : checkedToI64 c = .value i := by
  obtain ⟨hi, _, hc, hv⟩ := (checkedFromI64_value_iff _ _ _).mp h
  exact (checkedToI64_value_iff _ _).mpr ⟨hc, hv.symm, hi⟩

end ANL.Word
