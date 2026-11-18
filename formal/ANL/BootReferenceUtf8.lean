module
public import Init.Data.String.Lemmas.Iterate

public section
namespace ANL.Boot.Reference.Text

/-- Mathematical character-byte sum; not a separate runtime counter. -/
@[expose] def charBytes (chars : List Char) : Nat := (chars.map Char.utf8Size).sum

theorem ofList_bytes (chars : List Char) :
    (String.ofList chars).utf8ByteSize = charBytes chars := by
  induction chars with
  | nil => rfl
  | cons c cs ih =>
    have parts : String.ofList (c :: cs) = String.singleton c ++ String.ofList cs := by
      rw [String.singleton_eq_ofList, ← String.ofList_append]
      rfl
    rw [parts, String.utf8ByteSize_append, String.utf8ByteSize_singleton, ih]
    rfl

theorem toList_bytes (text : String) : charBytes text.toList = text.utf8ByteSize := by
  rw [← ofList_bytes, String.ofList_toList]

theorem toUTF8_bytes (text : String) : text.toUTF8.size = text.utf8ByteSize := rfl

end ANL.Boot.Reference.Text
