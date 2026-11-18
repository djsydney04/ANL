import ANL.WordCore

namespace ANL.Word

@[simp] theorem Width.bits_pos (w : Width) : 0 < w.bits := by cases w <;> decide
@[simp] theorem Width.modulus_pos (w : Width) : 0 < w.modulus := by
  exact Nat.pow_pos (by decide)

theorem Width.bits_allowed (w : Width) :
    w.bits = 8 ∨ w.bits = 16 ∨ w.bits = 32 ∨ w.bits = 64 := by
  cases w <;> simp [Width.bits]

@[simp] theorem Width.decode_bits (w : Width) : Width.decode w.bits = some w := by
  cases w <;> rfl

theorem Width.decode_iff (n : Nat) (w : Width) : Width.decode n = some w ↔ n = w.bits := by
  cases w <;> simp only [Width.bits, Width.decode] <;> split <;> simp_all

theorem Width.modulus_le_u64 (w : Width) : w.modulus ≤ 18446744073709551616 := by
  cases w <;> decide

theorem valid_u64_bound {a : Word} (h : Valid a) : a.value ≤ 18446744073709551615 := by
  have := a.width.modulus_le_u64
  unfold Valid at h
  omega

@[simp] theorem valid_mk (w : Width) (n : Nat) : Valid ⟨w, n⟩ ↔ n < w.modulus := Iff.rfl

theorem lowBits_lt (w : Width) (i : Int) : lowBits w i < w.modulus := by
  have hp : (0 : Int) < w.modulus := by exact_mod_cast w.modulus_pos
  have hlo := Int.emod_nonneg i (by omega : (w.modulus : Int) ≠ 0)
  have hhi := Int.emod_lt_of_pos i hp
  unfold lowBits
  omega

theorem lowBits_as_int (w : Width) (i : Int) :
    (lowBits w i : Int) = i % (w.modulus : Int) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by have := w.modulus_pos; omega)

theorem lowBits_nat (w : Width) (n : Nat) : lowBits w (n : Int) = n % w.modulus := by
  simp only [lowBits, Int.ofNat_mod_ofNat, Int.toNat_natCast]

theorem checkedInteger_value_iff (w : Width) (i : Int) (c : Word) :
    checkedInteger w i = .value c ↔ c.width = w ∧ Valid c ∧ (c.value : Int) = i := by
  unfold checkedInteger
  split
  next h =>
    constructor
    · intro e
      cases e
      simp only [valid_mk, true_and]
      constructor <;> omega
    · rintro ⟨hw, hv, hi⟩
      cases c with
      | mk cw cn =>
        simp only at hw hi
        subst cw
        have : i.toNat = cn := by omega
        simp [this]
  next h =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨hw, hv, hi⟩
    unfold Valid at hv
    rw [hw] at hv
    omega

theorem checkedInteger_trap_iff (w : Width) (i : Int) (t : Trap) :
    checkedInteger w i = .trap t ↔ t = .overflow ∧ ¬ (0 ≤ i ∧ i < (w.modulus : Int)) := by
  simp only [checkedInteger]
  split <;> simp_all [eq_comm]

@[simp] theorem checkedInteger_ne_invalid (w : Width) (i : Int) :
    checkedInteger w i ≠ .invalidInput := by
  unfold checkedInteger
  split <;> simp

/-- Mathematical payload equations, independent of the executable functions. -/
def BinaryPayload (op : BinaryOp) (w : Width) (a b c : Nat) : Prop :=
  match op with
  | .add => (c : Int) = (a : Int) + (b : Int)
  | .sub => (c : Int) = (a : Int) - (b : Int)
  | .mul => (c : Int) = (a : Int) * (b : Int)
  | .div => b ≠ 0 ∧ c = a / b
  | .rem => b ≠ 0 ∧ c = a % b
  | .wrapAdd => (c : Int) = ((a : Int) + (b : Int)) % (w.modulus : Int)
  | .wrapSub => (c : Int) = ((a : Int) - (b : Int)) % (w.modulus : Int)
  | .wrapMul => (c : Int) = ((a : Int) * (b : Int)) % (w.modulus : Int)
  | .bitAnd => c = a &&& b
  | .bitOr => c = a ||| b
  | .bitXor => c = a ^^^ b

/-- Under valid same-width inputs, these and only these arithmetic conditions trap. -/
def BinaryTrap (op : BinaryOp) (w : Width) (a b : Nat) (t : Trap) : Prop :=
  match op with
  | .add => t = .overflow ∧ w.modulus ≤ a + b
  | .sub => t = .overflow ∧ a < b
  | .mul => t = .overflow ∧ w.modulus ≤ a * b
  | .div | .rem => t = .divisionByZero ∧ b = 0
  | .wrapAdd | .wrapSub | .wrapMul | .bitAnd | .bitOr | .bitXor => False

/-- Independent valid-result judgment for the complete raw binary boundary. -/
def BinaryValue (op : BinaryOp) (a b c : Word) : Prop :=
  Compatible a b ∧ c.width = a.width ∧ Valid c ∧
    BinaryPayload op a.width a.value b.value c.value

theorem modulo_value_iff (w : Width) (i : Int) (c : Word) :
    (Outcome.value ⟨w, lowBits w i⟩ : Outcome Word) = .value c ↔
      c.width = w ∧ Valid c ∧ (c.value : Int) = i % (w.modulus : Int) := by
  constructor
  · intro h; cases h
    exact ⟨rfl, lowBits_lt w i, lowBits_as_int w i⟩
  · rintro ⟨hw, _, hv⟩
    cases c with
    | mk cw cn =>
      simp only at hw hv
      subst cw
      have he := lowBits_as_int w i
      have : lowBits w i = cn := by omega
      simp [this]

theorem calculate_value_iff (op : BinaryOp) (w : Width) (a b : Nat)
    (ha : a < w.modulus) (hb : b < w.modulus) (c : Word) :
    calculate op w a b = .value c ↔
      c.width = w ∧ Valid c ∧ BinaryPayload op w a b c.value := by
  cases op with
  | add | sub | mul => exact checkedInteger_value_iff _ _ _
  | div =>
    have bound : a / b < w.modulus := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
    by_cases hz : b = 0
    · simp [calculate, BinaryPayload, hz]
    · cases c with
      | mk cw cn =>
        simp [calculate, BinaryPayload, hz, Valid, Word.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩; exact ⟨rfl, bound, rfl⟩
        · rintro ⟨rfl, _, rfl⟩; exact ⟨rfl, rfl⟩
  | rem =>
    by_cases hz : b = 0
    · simp [calculate, BinaryPayload, hz]
    · have bound : a % b < w.modulus := Nat.lt_trans (Nat.mod_lt _ (by omega)) hb
      cases c with
      | mk cw cn =>
        simp [calculate, BinaryPayload, hz, Valid, Word.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩; exact ⟨rfl, bound, rfl⟩
        · rintro ⟨rfl, _, rfl⟩; exact ⟨rfl, rfl⟩
  | wrapAdd => exact modulo_value_iff w ((a : Int) + (b : Int)) c
  | wrapSub => exact modulo_value_iff w ((a : Int) - (b : Int)) c
  | wrapMul => exact modulo_value_iff w ((a : Int) * (b : Int)) c
  | bitAnd =>
    have bound : a &&& b < w.modulus := Nat.and_lt_two_pow a hb
    cases c with
    | mk cw cn =>
      simp [calculate, BinaryPayload, Valid, Word.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, bound, rfl⟩
      · rintro ⟨rfl, _, rfl⟩; exact ⟨rfl, rfl⟩
  | bitOr =>
    have bound : a ||| b < w.modulus := Nat.or_lt_two_pow ha hb
    cases c with
    | mk cw cn =>
      simp [calculate, BinaryPayload, Valid, Word.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, bound, rfl⟩
      · rintro ⟨rfl, _, rfl⟩; exact ⟨rfl, rfl⟩
  | bitXor =>
    have bound : a ^^^ b < w.modulus := Nat.xor_lt_two_pow ha hb
    cases c with
    | mk cw cn =>
      simp [calculate, BinaryPayload, Valid, Word.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, bound, rfl⟩
      · rintro ⟨rfl, _, rfl⟩; exact ⟨rfl, rfl⟩

theorem calculate_trap_iff (op : BinaryOp) (w : Width) (a b : Nat)
    (ha : a < w.modulus) (_hb : b < w.modulus) (t : Trap) :
    calculate op w a b = .trap t ↔ BinaryTrap op w a b t := by
  cases op with
  | add =>
    simp only [calculate, checkedInteger_trap_iff, BinaryTrap]
    constructor <;> rintro ⟨ht, h⟩ <;> exact ⟨ht, by omega⟩
  | sub =>
    simp only [calculate, checkedInteger_trap_iff, BinaryTrap]
    constructor <;> rintro ⟨ht, h⟩ <;> exact ⟨ht, by omega⟩
  | mul =>
    simp only [calculate, checkedInteger_trap_iff, BinaryTrap, ← Int.natCast_mul]
    constructor <;> rintro ⟨ht, h⟩ <;> exact ⟨ht, by omega⟩
  | div | rem => by_cases h : b = 0 <;> simp [calculate, BinaryTrap, h, eq_comm]
  | wrapAdd | wrapSub | wrapMul | bitAnd | bitOr | bitXor => simp [calculate, BinaryTrap]

@[simp] theorem calculate_ne_invalid (op : BinaryOp) (w : Width) (a b : Nat) :
    calculate op w a b ≠ .invalidInput := by
  cases op <;> simp only [calculate]
  all_goals first | exact checkedInteger_ne_invalid _ _ | split <;> simp | simp

theorem binary_value_iff (op : BinaryOp) (a b c : Word) :
    binary op a b = .value c ↔ BinaryValue op a b c := by
  unfold binary BinaryValue
  by_cases h : Compatible a b
  · have hb : b.value < a.width.modulus := by simpa [Valid, h.2.2] using h.2.1
    simp only [h, ite_true, true_and]
    exact calculate_value_iff _ _ _ _ h.1 hb _
  · simp [h]

theorem binary_trap_iff (op : BinaryOp) (a b : Word) (t : Trap) :
    binary op a b = .trap t ↔
      Compatible a b ∧ BinaryTrap op a.width a.value b.value t := by
  unfold binary
  by_cases h : Compatible a b
  · have hb : b.value < a.width.modulus := by simpa [Valid, h.2.2] using h.2.1
    simp only [h, ite_true, true_and]
    exact calculate_trap_iff _ _ _ _ h.1 hb _
  · simp [h]

theorem binary_invalid_iff (op : BinaryOp) (a b : Word) :
    binary op a b = .invalidInput ↔ ¬ Compatible a b := by
  unfold binary
  split <;> simp_all

theorem binary_value_valid {op : BinaryOp} {a b c : Word}
    (h : binary op a b = .value c) : Valid c := (binary_value_iff _ _ _ _).mp h |>.2.2.1

theorem binary_deterministic {op : BinaryOp} {a b : Word} {x y : Outcome Word}
    (hx : binary op a b = x) (hy : binary op a b = y) : x = y := hx.symm.trans hy

end ANL.Word
