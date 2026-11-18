import ANL.BootNativeFrame

namespace ANL.Boot.NativeByte

open ANL.Boot.NativeFrame
universe u

abbrev Memory := Word → Byte

def SupportedWidth (width : Nat) : Prop :=
  width = 1 ∨ width = 2 ∨ width = 4 ∨ width = 8

theorem supported_positive (supported : SupportedWidth width) : 0 < width := by
  rcases supported with rfl | rfl | rfl | rfl <;> omega

theorem supported_power_bound (supported : SupportedWidth width) :
    256 ^ width ≤ modulus := by
  rcases supported with rfl | rfl | rfl | rfl <;> decide

def low8 (value : Word) : Byte :=
  ⟨value.val % 256, Nat.mod_lt _ (by decide)⟩

def word (value : Nat) : Word :=
  ⟨value % modulus, Nat.mod_lt _ (by decide)⟩

def byteAt (value : Word) (index : Nat) : Byte :=
  ⟨(value.val / 256 ^ index) % 256, Nat.mod_lt _ (by decide)⟩

private theorem byte_dvd_modulus : 256 ∣ modulus := by decide

theorem low8_word (value : Nat) : (low8 (word value)).val = value % 256 := by
  change (value % modulus) % 256 = value % 256
  exact Nat.mod_mod_of_dvd value byte_dvd_modulus

theorem byteAt_zero (value : Word) : byteAt value 0 = low8 value := by
  apply Fin.ext
  simp [byteAt, low8]

def encodeLE : List Byte → Nat
  | [] => 0
  | first :: rest => first.val + 256 * encodeLE rest

theorem encodeLE_cons_mod (first : Byte) (rest : List Byte) :
    encodeLE (first :: rest) % 256 = first.val := by
  change (first.val + 256 * encodeLE rest) % 256 = first.val
  rw [Nat.add_mod, Nat.mul_mod_right]
  simp [Nat.mod_eq_of_lt first.isLt]

theorem encodeLE_bound (bytes : List Byte) :
    encodeLE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [encodeLE]
  | cons first rest ih =>
      have byteBound := first.isLt
      simp only [encodeLE, List.length_cons, Nat.pow_succ]
      omega

def window (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) : List Byte :=
  List.ofFn fun index : Fin width =>
    memory ⟨address.val + index.val, by have := index.isLt; omega⟩

def rawLoad (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) : Nat :=
  encodeLE (window memory address width span)

theorem rawLoad_bound (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) :
    rawLoad memory address width span < 256 ^ width := by
  simpa [rawLoad, window] using encodeLE_bound (window memory address width span)

theorem rawLoad_mod (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (positive : 0 < width) :
    rawLoad memory address width span % 256 = (memory address).val := by
  cases width with
  | zero => omega
  | succ width =>
      unfold rawLoad window
      rw [List.ofFn_succ, encodeLE_cons_mod]
      rfl

def unsignedLoad (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) : Word :=
  word (rawLoad memory address width span)

def signedLoad (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) : Word :=
  let value := rawLoad memory address width span
  if value < 256 ^ width / 2 then unsignedLoad memory address width span
  else word (value + (modulus - 256 ^ width))

theorem unsignedLoad_low8 (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (supported : SupportedWidth width) :
    low8 (unsignedLoad memory address width span) = memory address := by
  apply Fin.ext
  change (low8 (word (rawLoad memory address width span))).val = _
  rw [low8_word]
  exact rawLoad_mod memory address width span (supported_positive supported)

private theorem signed_adjustment_mod (supported : SupportedWidth width) :
    (modulus - 256 ^ width) % 256 = 0 := by
  rcases supported with rfl | rfl | rfl | rfl <;> decide

theorem signedLoad_low8 (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (supported : SupportedWidth width) :
    low8 (signedLoad memory address width span) = memory address := by
  dsimp only [signedLoad]
  split
  · exact unsignedLoad_low8 memory address width span supported
  · apply Fin.ext
    rw [low8_word, Nat.add_mod, signed_adjustment_mod supported, Nat.add_zero, Nat.mod_mod]
    exact rawLoad_mod memory address width span (supported_positive supported)

def storeLE (memory : Memory) (address : Word) (width : Nat)
    (_span : address.val + width ≤ modulus) (value : Word) (location : Word) : Byte :=
  if address.val ≤ location.val ∧ location.val < address.val + width then
    byteAt value (location.val - address.val)
  else memory location

theorem storeLE_base (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (positive : 0 < width) (value : Word) :
    storeLE memory address width span value address = low8 value := by
  have inside : address.val ≤ address.val ∧ address.val < address.val + width := by omega
  simp [storeLE, inside, byteAt_zero]

theorem storeLE_outside (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (value : Word) (location : Word)
    (outside : ¬ (address.val ≤ location.val ∧ location.val < address.val + width)) :
    storeLE memory address width span value location = memory location := by
  simp [storeLE, outside]

theorem storeLE_index (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (value : Word) (index : Nat)
    (within : index < width) :
    storeLE memory address width span value
      ⟨address.val + index, by omega⟩ = byteAt value index := by
  unfold storeLE
  rw [ite_eq_left (by constructor <;> dsimp <;> omega)]
  congr 1
  simp

theorem unsignedLoad_after_store (memory : Memory) (address : Word)
    (storeWidth loadWidth : Nat) (storeSpan : address.val + storeWidth ≤ modulus)
    (loadSpan : address.val + loadWidth ≤ modulus)
    (storeSupported : SupportedWidth storeWidth) (loadSupported : SupportedWidth loadWidth)
    (value : Word) :
    low8 (unsignedLoad (storeLE memory address storeWidth storeSpan value)
      address loadWidth loadSpan) = low8 value := by
  rw [unsignedLoad_low8 _ _ _ _ loadSupported]
  exact storeLE_base memory address storeWidth storeSpan (supported_positive storeSupported) value

theorem signedLoad_after_store (memory : Memory) (address : Word)
    (storeWidth loadWidth : Nat) (storeSpan : address.val + storeWidth ≤ modulus)
    (loadSpan : address.val + loadWidth ≤ modulus)
    (storeSupported : SupportedWidth storeWidth) (loadSupported : SupportedWidth loadWidth)
    (value : Word) :
    low8 (signedLoad (storeLE memory address storeWidth storeSpan value)
      address loadWidth loadSpan) = low8 value := by
  rw [signedLoad_low8 _ _ _ _ loadSupported]
  exact storeLE_base memory address storeWidth storeSpan (supported_positive storeSupported) value

inductive Fact (Origin : Type u) where
  | unknown
  | constant (value : Byte)
  | origin (value : Origin)

variable {Origin : Type u}

def Holds (valuation : Origin → Byte) : Fact Origin → Byte → Prop
  | .unknown, _ => True
  | .constant expected, actual => actual = expected
  | .origin token, actual => actual = valuation token

def MemHolds (valuation : Origin → Byte) (facts : Word → Fact Origin) (memory : Memory) : Prop :=
  ∀ location, Holds valuation (facts location) (memory location)

def overwrite (facts : Word → Fact Origin) (address : Word) (width : Nat)
    (_span : address.val + width ≤ modulus) (fact : Fact Origin) (location : Word) : Fact Origin :=
  if location = address then fact
  else if address.val ≤ location.val ∧ location.val < address.val + width then .unknown
  else facts location

theorem store_preserves (valuation : Origin → Byte) (facts : Word → Fact Origin)
    (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (positive : 0 < width)
    (value : Word) (fact : Fact Origin)
    (before : MemHolds valuation facts memory) (known : Holds valuation fact (low8 value)) :
    MemHolds valuation (overwrite facts address width span fact)
      (storeLE memory address width span value) := by
  intro location
  by_cases base : location = address
  · subst location
    simpa [overwrite, storeLE_base memory address width span positive value] using known
  · by_cases inside : address.val ≤ location.val ∧ location.val < address.val + width
    · simp [overwrite, base, inside, Holds]
    · simpa [overwrite, base, inside, storeLE] using before location

theorem unsignedLoad_preserves (valuation : Origin → Byte) (facts : Word → Fact Origin)
    (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (supported : SupportedWidth width)
    (before : MemHolds valuation facts memory) :
    Holds valuation (facts address) (low8 (unsignedLoad memory address width span)) := by
  rw [unsignedLoad_low8 memory address width span supported]
  exact before address

theorem signedLoad_preserves (valuation : Origin → Byte) (facts : Word → Fact Origin)
    (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (supported : SupportedWidth width)
    (before : MemHolds valuation facts memory) :
    Holds valuation (facts address) (low8 (signedLoad memory address width span)) := by
  rw [signedLoad_low8 memory address width span supported]
  exact before address

end ANL.Boot.NativeByte

