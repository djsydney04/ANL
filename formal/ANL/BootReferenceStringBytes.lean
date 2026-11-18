import ANL.MemoryWireIO
import ANL.BootReferenceJsonString

namespace ANL.Boot.Reference.Text

theorem truncateChars_bytes (chars : List Char) (budget : Nat) :
    charBytes (ANL.Memory.Wire.IOBoundary.truncateChars chars budget) ≤ budget := by
  induction chars generalizing budget with
  | nil => simp [ANL.Memory.Wire.IOBoundary.truncateChars, charBytes]
  | cons c cs ih =>
    rw [ANL.Memory.Wire.IOBoundary.truncateChars]
    split
    · have bound := ih (budget - c.utf8Size)
      simp only [charBytes, List.map_cons, List.sum_cons] at ⊢ bound
      omega
    · simp [charBytes]

theorem truncateChars_prefix (chars : List Char) (budget : Nat) :
    (ANL.Memory.Wire.IOBoundary.truncateChars chars budget).IsPrefix chars := by
  induction chars generalizing budget with
  | nil => exact ⟨[], rfl⟩
  | cons c cs ih =>
    rw [ANL.Memory.Wire.IOBoundary.truncateChars]
    split
    · obtain ⟨rest, equal⟩ := ih (budget - c.utf8Size)
      exact ⟨rest, by simp [equal]⟩
    · exact ⟨c :: cs, rfl⟩

theorem reason_bytes (text : String) :
    (ANL.Memory.Wire.IOBoundary.reason text).toUTF8.size ≤ 1024 := by
  rw [toUTF8_bytes, ANL.Memory.Wire.IOBoundary.reason, ofList_bytes]
  exact truncateChars_bytes _ _

theorem reason_characters_prefix (text : String) :
    (ANL.Memory.Wire.IOBoundary.reason text).toList.IsPrefix text.toList := by
  simpa [ANL.Memory.Wire.IOBoundary.reason] using truncateChars_prefix text.toList 1024


theorem quoted_reason_bytes (text : String) :
    (Lean.Json.renderString (ANL.Memory.Wire.IOBoundary.reason text)).toUTF8.size ≤ 6146 := by
  have bounded := reason_bytes text
  have rendered := quoted_bytes (ANL.Memory.Wire.IOBoundary.reason text)
  omega


end ANL.Boot.Reference.Text
