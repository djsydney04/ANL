import ANL.BootSummaryWriterCore

namespace ANL.Boot.Reference.Summary
open Lean

/-- Characters that can occur literally inside a quoted JSON string. -/
def SafeASCII (value : String) : Prop :=
  ∀ c ∈ value.toList, 32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '"' ∧ c ≠ '\\'

/-- Canonical decimal meaning independent of a writer or its return value. -/
structure Decimal (value : Nat) (token : String) : Prop where
  digits : ∀ c ∈ token.toList, c.isDigit = true
  value : Nat.ofDigitChars 10 token.toList 0 = value
  nonempty : token.toList ≠ []
  leading : token.toList.head? = some '0' → token = "0"

/-- No commas occur before the first or after the last element. -/
def commaBefore (remaining : List α) : ByteArray :=
  if remaining.isEmpty then ByteArray.empty else ",".toUTF8

mutual
/-- JSON structure/value meaning relative to the existing total string-escape leaf.
`libraryString` intentionally retains that library's parser-level escaping trust boundary. -/
inductive Wire : Json → ByteArray → Prop where
  | null : Wire .null "null".toUTF8
  | boolean (value : Bool) : Wire (.bool value) (if value then "true" else "false").toUTF8
  | natural : Decimal value token → Wire (toJson value) token.toUTF8
  | ascii : SafeASCII value → Wire (.str value) (quoted value).toUTF8
  | libraryString (value : String) : Wire (.str value) (Json.renderString value).toUTF8
  | array : Elements values bytes → Wire (toJson values) ("[".toUTF8 ++ bytes ++ "]".toUTF8)
  | object : Fields values bytes → (values.map Prod.fst).Nodup →
      Wire (Json.mkObj values) ("{".toUTF8 ++ bytes ++ "}".toUTF8)
inductive Elements : List Json → ByteArray → Prop where
  | nil : Elements [] ByteArray.empty
  | cons : Wire value head → Elements values tail →
      Elements (value :: values) (head ++ commaBefore values ++ tail)
inductive Fields : List (String × Json) → ByteArray → Prop where
  | nil : Fields [] ByteArray.empty
  | cons : SafeASCII key → Wire value head → Fields values tail →
      Fields ((key, value) :: values)
        ((quoted key).toUTF8 ++ ":".toUTF8 ++ head ++ commaBefore values ++ tail)
end

/-- The size bound is on the same actual fragment appended by the executable writer. -/
def Spec (write : Writer) (value : Json) (bound : Nat) : Prop :=
  ∃ bytes, Wire value bytes ∧ bytes.size ≤ bound ∧ Appends write bytes

/-- Field meaning retains exact names and values; object construction additionally requires unique keys. -/
def FieldSpec (writes : List (String × Writer)) (values : List (String × Json)) (bound : Nat) : Prop :=
  ∃ bytes, Fields values bytes ∧ bytes.size ≤ bound ∧ Appends (items field writes true) bytes

end ANL.Boot.Reference.Summary
