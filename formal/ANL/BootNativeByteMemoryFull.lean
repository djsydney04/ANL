import ANL.BootNativeByteMemory

namespace ANL.Boot.NativeByte.MemoryFull

open ANL.Boot.NativeFrame ANL.Boot.NativeByte

theorem encode_append (left right : List Byte) :
    encodeLE (left ++ right) = encodeLE left + 256 ^ left.length * encodeLE right := by
  induction left with
  | nil => simp [encodeLE]
  | cons first rest ih =>
      simp only [List.cons_append, encodeLE, List.length_cons, ih, Nat.pow_succ]
      rw [Nat.mul_add, Nat.add_assoc, Nat.mul_comm (256 ^ rest.length) 256, Nat.mul_assoc]

theorem encode_byte_prefix (value : Word) (width : Nat) :
    encodeLE (List.ofFn fun index : Fin width => byteAt value index.val) =
      value.val % 256 ^ width := by
  induction width with
  | zero => simp [encodeLE, Nat.mod_one]
  | succ width ih =>
      rw [List.ofFn_succ_last, encode_append]
      change encodeLE (List.ofFn fun index : Fin width => byteAt value index.val) +
        256 ^ (List.ofFn fun index : Fin width => byteAt value index.val).length *
          (byteAt value width).val = value.val % 256 ^ (width + 1)
      rw [ih, List.length_ofFn]
      exact (Nat.mod_pow_succ (x := value.val) (b := 256) (k := width)).symm

theorem window_after_store (memory : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (value : Word) :
    window (storeLE memory address width span value) address width span =
      List.ofFn (fun index : Fin width => byteAt value index.val) := by
  unfold window
  apply congrArg List.ofFn
  funext index
  exact storeLE_index memory address width span value index.val index.isLt

theorem rawLoad_store_eight (memory : Memory) (address : Word)
    (span : address.val + 8 ≤ modulus) (value : Word) :
    rawLoad (storeLE memory address 8 span value) address 8 span = value.val := by
  unfold rawLoad
  rw [window_after_store, encode_byte_prefix]
  have full : 256 ^ 8 = modulus := by decide
  rw [full]
  exact Nat.mod_eq_of_lt value.isLt

theorem unsignedLoad_store_eight (memory : Memory) (address : Word)
    (span : address.val + 8 ≤ modulus) (value : Word) :
    unsignedLoad (storeLE memory address 8 span value) address 8 span = value := by
  apply Fin.ext
  change rawLoad (storeLE memory address 8 span value) address 8 span % modulus = value.val
  rw [rawLoad_store_eight]
  exact Nat.mod_eq_of_lt value.isLt

theorem signedLoad_store_eight (memory : Memory) (address : Word)
    (span : address.val + 8 ≤ modulus) (value : Word) :
    signedLoad (storeLE memory address 8 span value) address 8 span = value := by
  have zeroAdjustment : modulus - 256 ^ 8 = 0 := by decide
  dsimp only [signedLoad]
  split
  · exact unsignedLoad_store_eight memory address span value
  · rw [zeroAdjustment, Nat.add_zero]
    exact unsignedLoad_store_eight memory address span value

def AgreesOn (before after : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) : Prop :=
  ∀ index : Fin width,
    after ⟨address.val + index.val, by have := index.isLt; omega⟩ =
      before ⟨address.val + index.val, by have := index.isLt; omega⟩

theorem agrees_trans (before middle after : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus)
    (first : AgreesOn before middle address width span)
    (second : AgreesOn middle after address width span) :
    AgreesOn before after address width span :=
  fun index => (second index).trans (first index)

theorem store_preserves_range (memory : Memory) (writeAddress : Word) (writeWidth : Nat)
    (writeSpan : writeAddress.val + writeWidth ≤ modulus) (value : Word)
    (savedAddress : Word) (savedWidth : Nat)
    (savedSpan : savedAddress.val + savedWidth ≤ modulus)
    (separated : writeAddress.val + writeWidth ≤ savedAddress.val ∨
      savedAddress.val + savedWidth ≤ writeAddress.val) :
    AgreesOn memory (storeLE memory writeAddress writeWidth writeSpan value)
      savedAddress savedWidth savedSpan := by
  intro index
  apply storeLE_outside
  have inside := index.isLt
  rcases separated with left | right
  · dsimp
    omega
  · dsimp
    omega

theorem window_eq_of_agrees (before after : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (agree : AgreesOn before after address width span) :
    window after address width span = window before address width span := by
  unfold window
  apply congrArg List.ofFn
  funext index
  exact agree index

theorem rawLoad_eq_of_agrees (before after : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (agree : AgreesOn before after address width span) :
    rawLoad after address width span = rawLoad before address width span :=
  congrArg encodeLE (window_eq_of_agrees before after address width span agree)

theorem unsignedLoad_eq_of_agrees (before after : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (agree : AgreesOn before after address width span) :
    unsignedLoad after address width span = unsignedLoad before address width span :=
  congrArg word (rawLoad_eq_of_agrees before after address width span agree)

theorem signedLoad_eq_of_agrees (before after : Memory) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (agree : AgreesOn before after address width span) :
    signedLoad after address width span = signedLoad before address width span := by
  simp only [signedLoad, unsignedLoad, rawLoad_eq_of_agrees before after address width span agree]

theorem reload_saved_eight (memory after : Memory) (address : Word)
    (span : address.val + 8 ≤ modulus) (value : Word)
    (saved : AgreesOn (storeLE memory address 8 span value) after address 8 span) :
    unsignedLoad after address 8 span = value ∧ signedLoad after address 8 span = value :=
  ⟨(unsignedLoad_eq_of_agrees (storeLE memory address 8 span value) after address 8 span saved).trans
      (unsignedLoad_store_eight memory address span value),
   (signedLoad_eq_of_agrees (storeLE memory address 8 span value) after address 8 span saved).trans
      (signedLoad_store_eight memory address span value)⟩

end ANL.Boot.NativeByte.MemoryFull
