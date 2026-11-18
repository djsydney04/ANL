module
public import ANL.BootReferenceUtf8
public import Lean.Data.Json.Printer
import all Lean.Data.Json.Printer
import all Init.Data.Repr

public section

namespace ANL.Boot.Reference.Text
open Lean

private theorem digitChar_utf8 (n : Nat) : n.digitChar.utf8Size = 1 := by
  by_cases h0 : n = 0
  · subst n; rfl
  by_cases h1 : n = 1
  · subst n; rfl
  by_cases h2 : n = 2
  · subst n; rfl
  by_cases h3 : n = 3
  · subst n; rfl
  by_cases h4 : n = 4
  · subst n; rfl
  by_cases h5 : n = 5
  · subst n; rfl
  by_cases h6 : n = 6
  · subst n; rfl
  by_cases h7 : n = 7
  · subst n; rfl
  by_cases h8 : n = 8
  · subst n; rfl
  by_cases h9 : n = 9
  · subst n; rfl
  by_cases h10 : n = 10
  · subst n; rfl
  by_cases h11 : n = 11
  · subst n; rfl
  by_cases h12 : n = 12
  · subst n; rfl
  by_cases h13 : n = 13
  · subst n; rfl
  by_cases h14 : n = 14
  · subst n; rfl
  by_cases h15 : n = 15
  · subst n; rfl
  simp only [Nat.digitChar, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, ite_false]
  rfl

/-- Bound the actual library character escape, including its accumulator. -/
private theorem escapeAux_bytes (acc : String) (c : Char) :
    (Json.escapeAux acc c).utf8ByteSize ≤ acc.utf8ByteSize + 6 * c.utf8Size := by
  unfold Json.escapeAux
  split
  · next h => subst c; simp; decide
  · split
    · next h => subst c; simp; decide
    · split
      · next h => subst c; simp; decide
      · split
        · next h => subst c; simp; decide
        · split
          · simp; omega
          · simp only [String.utf8ByteSize_append, String.utf8ByteSize_push, digitChar_utf8]
            have positive := c.utf8Size_pos
            change acc.utf8ByteSize + 2 + 1 + 1 + 1 + 1 ≤ acc.utf8ByteSize + 6 * c.utf8Size
            omega

private theorem escapeFold_bytes (chars : List Char) (acc : String) :
    (chars.foldl Json.escapeAux acc).utf8ByteSize ≤ acc.utf8ByteSize + 6 * charBytes chars := by
  induction chars generalizing acc with
  | nil => simp [charBytes]
  | cons c cs ih =>
    have tail := ih (Json.escapeAux acc c)
    have first := escapeAux_bytes acc c
    simp only [List.foldl_cons, charBytes, List.map_cons, List.sum_cons]
    simp only [charBytes] at tail
    omega

theorem escape_bytes (text acc : String) :
    (Json.escape text acc).utf8ByteSize ≤ acc.utf8ByteSize + 6 * text.utf8ByteSize := by
  unfold Json.escape
  split
  · rw [String.foldl_eq_foldl_toList]
    simpa [toList_bytes] using escapeFold_bytes text.toList acc
  · simp; omega

theorem renderString_bytes (text acc : String) :
    (Json.renderString text acc).toUTF8.size ≤ acc.toUTF8.size + 6 * text.toUTF8.size + 2 := by
  simp only [toUTF8_bytes, Json.renderString, String.utf8ByteSize_append]
  have bound := escape_bytes text (acc ++ "\"")
  simp only [String.utf8ByteSize_append] at bound
  change (Json.escape text (acc ++ "\"")).utf8ByteSize + 1 ≤ acc.utf8ByteSize + 6 * text.utf8ByteSize + 2
  change (Json.escape text (acc ++ "\"")).utf8ByteSize ≤ acc.utf8ByteSize + 1 + 6 * text.utf8ByteSize at bound
  omega

theorem quoted_bytes (text : String) :
    (Json.renderString text).toUTF8.size ≤ 6 * text.toUTF8.size + 2 := by
  simpa using renderString_bytes text ""


end ANL.Boot.Reference.Text
