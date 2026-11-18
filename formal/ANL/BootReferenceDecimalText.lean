import Init.Data.Nat.ToString
import Init.Data.String.Decode
import Init.Data.Char.Lemmas
import Init.Omega

namespace ANL.Boot.Reference.Text

theorem repr_isDigit {n : Nat} {c : Char} (hc : c ∈ n.repr.toList) :
    c.isDigit := by
  rw [Nat.toList_repr] at hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

theorem repr_ascii {n : Nat} {c : Char} (hc : c ∈ n.repr.toList) :
    c.toNat < 128 := by
  have hd := Char.isDigit_iff_toNat.mp (repr_isDigit hc)
  have hu : c.toNat ≤ 57 := by simpa using hd.2
  omega

private theorem digitChar_utf8Size {n : Nat} (hn : n < 10) :
    n.digitChar.utf8Size = 1 := by
  apply Char.utf8Size_eq_one_iff.mpr
  rw [UInt32.le_iff_toNat_le]
  have hd := Nat.toNat_digitChar_of_lt_ten hn
  change n.digitChar.val.toNat = 48 + n at hd
  simp only [UInt32.reduceToNat]
  omega

theorem repr_utf8ByteSize_eq_length (n : Nat) :
    n.repr.utf8ByteSize = n.repr.length := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 10
    · rw [Nat.repr_of_lt hn]
      simp only [String.utf8ByteSize_singleton, String.length_singleton]
      exact digitChar_utf8Size hn
    · rw [Nat.repr_of_ge (by omega)]
      simp only [String.utf8ByteSize_append, String.length_append,
        String.utf8ByteSize_singleton, String.length_singleton]
      rw [digitChar_utf8Size (Nat.mod_lt _ (by decide)),
        ih (n / 10) (Nat.div_lt_self (by omega) (by decide))]

theorem repr_toUTF8_size_eq_length (n : Nat) :
    n.repr.toUTF8.size = n.repr.length := by
  simpa only [String.toUTF8_eq_toByteArray, String.size_toByteArray] using
    repr_utf8ByteSize_eq_length n

theorem repr_toUTF8_size_le_twenty {n : Nat} (hn : n ≤ 18446744073709551615) :
    n.repr.toUTF8.size ≤ 20 := by
  rw [repr_toUTF8_size_eq_length]
  apply (Nat.length_repr_le_iff (by decide)).mpr
  have hp : 18446744073709551615 < 10 ^ 20 := by decide
  omega

theorem repr_toUTF8_size_le_three {n : Nat} (hn : n < 256) :
    n.repr.toUTF8.size ≤ 3 := by
  rw [repr_toUTF8_size_eq_length]
  apply (Nat.length_repr_le_iff (by decide)).mpr
  have hp : 256 < 10 ^ 3 := by decide
  omega

theorem repr_value (n : Nat) : Nat.ofDigitChars 10 n.repr.toList 0 = n := by
  simp

theorem repr_nonempty (n : Nat) : n.repr.toList ≠ [] := by
  simp

theorem repr_leading_zero_iff (n : Nat) : n.repr.toList.head? = some '0' ↔ n = 0 := by
  simp only [Nat.toList_repr]
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 10
    · simp [Nat.toDigits_of_lt_base hn]
    · have hdiv : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
      have hpos : 0 < n / 10 := Nat.div_pos (by omega) (by decide)
      have hhead := ih (n / 10) hdiv
      rw [Nat.toDigits_of_base_le (by decide) (by omega)]
      cases he : Nat.toDigits 10 (n / 10) with
      | nil => exact False.elim (Nat.toDigits_ne_nil he)
      | cons c cs =>
        simp only [he, List.head?_cons] at hhead
        simp only [List.cons_append, List.head?_cons]
        simpa [Nat.ne_of_gt hpos, Nat.ne_of_gt (by omega : 0 < n)] using hhead

theorem repr_no_leading_zero {n : Nat} (hn : n ≠ 0) :
    n.repr.toList.head? ≠ some '0' := by
  exact fun h => hn ((repr_leading_zero_iff n).mp h)

end ANL.Boot.Reference.Text
