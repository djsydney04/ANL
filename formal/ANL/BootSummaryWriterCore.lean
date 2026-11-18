import ANL.BootReferenceOutputBounds
import ANL.BootReferenceDecimalText
import ANL.BootReferenceStringBytes

namespace ANL.Boot.Reference.Summary
open Lean Output

abbrev Writer := Buffer → Except Output.ExportError Buffer

def text (value : String) : Writer := fun buffer => appendText buffer value

def empty : Writer := fun buffer => .ok buffer

def seq (first second : Writer) : Writer := fun buffer => do
  second (← first buffer)

def quoted (value : String) : String := "\"" ++ value ++ "\""

def ascii (value : String) : Writer := text (quoted value)
def natural (value : Nat) : Writer := text value.repr
def word (value : Nat) : Writer := ascii value.repr
def diagnostic (value : String) : Writer := text (Json.renderString value)
def null : Writer := text "null"
def boolean (value : Bool) : Writer := text (if value then "true" else "false")

def optional (write : α → Writer) : Option α → Writer
  | none => null | some value => write value

/-- The only unbounded container traversal is a tail call after each bounded append. -/
def items (write : α → Writer) : List α → Bool → Writer
  | [], _, buffer => .ok buffer
  | value :: rest, first, buffer => do
      let buffer ← if first then .ok buffer else text "," buffer
      let buffer ← write value buffer
      items write rest false buffer

def array (write : α → Writer) (values : List α) : Writer :=
  seq (text "[") (seq (items write values true) (text "]"))

def field (binding : String × Writer) : Writer :=
  seq (ascii binding.1) (seq (text ":") binding.2)

def object (fields : List (String × Writer)) : Writer :=
  seq (text "{") (seq (items field fields true) (text "}"))

/-- An actual successful append for every buffer with enough capacity for the stated bytes. -/
def Appends (write : Writer) (chunk : ByteArray) : Prop :=
  ∀ before : Buffer, before.bytes.size + chunk.size ≤ ANL.Memory.Reference.maxOutputBytes - 1 →
    ∃ after, write before = .ok after ∧ after.bytes = before.bytes ++ chunk

end ANL.Boot.Reference.Summary
