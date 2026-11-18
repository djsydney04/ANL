import ANL.BootSummaryWire

namespace ANL.Boot.Reference.Summary
open Lean Output

 theorem Appends.text (value : String) : Appends (Summary.text value) value.toUTF8 := by
  intro before enough
  refine ⟨⟨before.bytes ++ value.toUTF8, by simpa using enough⟩, ?_, rfl⟩
  simp only [Summary.text, appendText, ANL.Memory.Reference.Buffer.text,
    ANL.Memory.Reference.Buffer.append, dite_eq_left enough, Except.mapError]

 theorem Appends.empty : Appends Summary.empty ByteArray.empty := by
  intro before _
  exact ⟨before, rfl, (ByteArray.append_empty).symm⟩

 theorem Appends.seq (first : Appends left a) (second : Appends right b) :
    Appends (Summary.seq left right) (a ++ b) := by
  intro before enough
  simp only [ByteArray.size_append] at enough
  obtain ⟨middle, written, bytes⟩ := first before (by omega)
  have room : middle.bytes.size + b.size ≤ ANL.Memory.Reference.maxOutputBytes - 1 := by
    rw [bytes, ByteArray.size_append]
    omega
  obtain ⟨after, written', bytes'⟩ := second middle room
  refine ⟨after, ?_, ?_⟩
  · simp only [ANL.Boot.Reference.Summary.seq, written, bind, Except.bind, written']
  · rw [bytes', bytes, ByteArray.append_assoc]

 theorem Appends.items_nil (write : α → Writer) (first : Bool) :
    Appends (items write [] first) ByteArray.empty := Appends.empty

 theorem Appends.items_false (good : Appends (items write values true) bytes) :
    Appends (items write values false) (commaBefore values ++ bytes) := by
  cases values with
  | nil => simpa [commaBefore, items] using good
  | cons value rest =>
    have same : items write (value :: rest) false =
        Summary.seq (Summary.text ",") (items write (value :: rest) true) := by
      funext before
      simp only [items, ANL.Boot.Reference.Summary.seq]
      cases Summary.text "," before <;> rfl
    rw [same]
    simpa [commaBefore] using (Appends.text ",").seq good

 theorem Appends.items_cons (head : Appends (write value) a)
    (tail : Appends (items write rest true) b) :
    Appends (items write (value :: rest) true) (a ++ commaBefore rest ++ b) := by
  have same : items write (value :: rest) true =
      Summary.seq (write value) (items write rest false) := by
    funext before
    simp [items, ANL.Boot.Reference.Summary.seq, bind, Except.bind]
  rw [same, ByteArray.append_assoc]
  exact head.seq tail.items_false

 theorem Spec.mono (good : Spec write value bound) (larger : bound ≤ bound') :
    Spec write value bound' := by
  obtain ⟨bytes, meaning, size, appends⟩ := good
  exact ⟨bytes, meaning, Nat.le_trans size larger, appends⟩

 theorem decimalMeaning (n : Nat) : Decimal n n.repr := by
  refine ⟨fun _ hc => Text.repr_isDigit hc, Text.repr_value n, Text.repr_nonempty n, ?_⟩
  intro hz
  have equal := (Text.repr_leading_zero_iff n).mp hz
  subst n
  rfl

 theorem decimalASCII (n : Nat) : SafeASCII n.repr := by
  intro c hc
  have hd := Char.isDigit_iff_toNat.mp (Text.repr_isDigit hc)
  have lower : 48 ≤ c.toNat := by simpa using hd.1
  have upper : c.toNat ≤ 57 := by simpa using hd.2
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro equal
    subst c
    contradiction
  · intro equal
    subst c
    contradiction

 theorem quoted_size (value : String) :
    (quoted value).toUTF8.size = value.toUTF8.size + 2 := by
  simp only [quoted, String.toUTF8_eq_toByteArray, String.toByteArray_append,
    ByteArray.size_append]
  change 1 + value.toByteArray.size + 1 = value.toByteArray.size + 2
  omega

 theorem Spec.natural (bounded : n ≤ 18446744073709551615) :
    Spec (Summary.natural n) (toJson n) 20 :=
  ⟨n.repr.toUTF8, .natural (decimalMeaning n), Text.repr_toUTF8_size_le_twenty bounded,
    Appends.text _⟩

 theorem Spec.natural_byte (bounded : n < 256) :
    Spec (Summary.natural n) (toJson n) 3 :=
  ⟨n.repr.toUTF8, .natural (decimalMeaning n), Text.repr_toUTF8_size_le_three bounded,
    Appends.text _⟩

 theorem Spec.ascii (safe : SafeASCII value) :
    Spec (Summary.ascii value) (.str value) (value.toUTF8.size + 2) :=
  ⟨(quoted value).toUTF8, .ascii safe, Nat.le_of_eq (quoted_size value), Appends.text _⟩

 theorem Spec.word (bounded : n ≤ 18446744073709551615) :
    Spec (Summary.word n) (.str n.repr) 22 := by
  apply (Spec.ascii (decimalASCII n)).mono
  have size := Text.repr_toUTF8_size_le_twenty bounded
  omega

 theorem Spec.diagnostic (value : String) :
    Spec (Summary.diagnostic value) (.str value) (6 * value.toUTF8.size + 2) :=
  ⟨(Json.renderString value).toUTF8, .libraryString value, Text.quoted_bytes value,
    Appends.text _⟩

 theorem Spec.null : Spec Summary.null .null 4 :=
  ⟨"null".toUTF8, .null, by decide, Appends.text _⟩

 theorem Spec.boolean (value : Bool) : Spec (Summary.boolean value) (.bool value) 5 := by
  refine ⟨(if value then "true" else "false").toUTF8, .boolean value, ?_, Appends.text _⟩
  cases value <;> decide

 theorem Spec.optional (encode : α → Json) (value : Option α)
    (good : ∀ item, value = some item → Spec (write item) (encode item) bound)
    (nullBound : 4 ≤ bound) :
    Spec (Summary.optional write value) (value.elim .null encode) bound := by
  cases value with
  | none => exact Spec.null.mono nullBound
  | some item => exact good item rfl

 theorem commaBefore_size (values : List α) : (commaBefore values).size ≤ 1 := by
  cases values <;> simp [commaBefore] <;> decide

 theorem elementsSpec (write : α → Writer) (encode : α → Json) (values : List α)
    (good : ∀ item ∈ values, Spec (write item) (encode item) perItem) :
    ∃ bytes, Elements (values.map encode) bytes ∧ bytes.size ≤ values.length * (perItem + 1) ∧
      Appends (items write values true) bytes := by
  induction values with
  | nil => exact ⟨ByteArray.empty, .nil, by simp, Appends.items_nil _ _⟩
  | cons value rest ih =>
    obtain ⟨head, hm, hs, ha⟩ := good value (by simp)
    obtain ⟨tail, tm, ts, ta⟩ := ih (fun item member => good item (by simp [member]))
    refine ⟨head ++ commaBefore rest ++ tail, ?_, ?_, ha.items_cons ta⟩
    · have shape : commaBefore (rest.map encode) = commaBefore rest := by
        simp [commaBefore]
      simpa [shape] using Elements.cons hm tm
    · simp only [ByteArray.size_append, List.length_cons]
      have cs := commaBefore_size rest
      have arithmetic : (rest.length + 1) * (perItem + 1) =
          rest.length * (perItem + 1) + perItem + 1 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      omega

 theorem Spec.array (write : α → Writer) (encode : α → Json) (values : List α)
    (good : ∀ item ∈ values, Spec (write item) (encode item) perItem) :
    Spec (Summary.array write values) (toJson (values.map encode))
      (2 + values.length * (perItem + 1)) := by
  obtain ⟨bytes, meaning, size, appended⟩ := elementsSpec write encode values good
  refine ⟨"[".toUTF8 ++ bytes ++ "]".toUTF8, .array meaning, ?_, ?_⟩
  · simp only [ByteArray.size_append]
    change 1 + bytes.size + 1 ≤ _
    omega
  · have joined := (Appends.text "[").seq (appended.seq (Appends.text "]"))
    simpa [Summary.array, ByteArray.append_assoc] using joined

 theorem FieldSpec.nil : FieldSpec [] [] 0 :=
  ⟨ByteArray.empty, .nil, by decide, Appends.items_nil _ _⟩

 theorem FieldSpec.mono (good : FieldSpec writes values bound) (larger : bound ≤ bound') :
    FieldSpec writes values bound' := by
  obtain ⟨bytes, meaning, size, appends⟩ := good
  exact ⟨bytes, meaning, Nat.le_trans size larger, appends⟩

 theorem FieldSpec.cons (safe : SafeASCII key) (head : Spec write value valueBound)
    (tail : FieldSpec writes values restBound) (shape : writes.isEmpty = values.isEmpty) :
    FieldSpec ((key, write) :: writes) ((key, value) :: values)
      (key.toUTF8.size + 3 + valueBound + 1 + restBound) := by
  obtain ⟨a, am, az, aa⟩ := head
  obtain ⟨b, bm, bz, ba⟩ := tail
  have keySize := quoted_size key
  have commaSize := commaBefore_size values
  have commas : commaBefore writes = commaBefore values := by simp [commaBefore, shape]
  have fieldAppends : Appends (field (key, write)) ((quoted key).toUTF8 ++ ":".toUTF8 ++ a) := by
    have joined := (Appends.text (quoted key)).seq ((Appends.text ":").seq aa)
    simpa [field, Summary.ascii, ByteArray.append_assoc] using joined
  refine ⟨(quoted key).toUTF8 ++ ":".toUTF8 ++ a ++ commaBefore values ++ b,
    .cons safe am bm, ?_, ?_⟩
  · simp only [ByteArray.size_append]
    change (quoted key).toUTF8.size + 1 + a.size + (commaBefore values).size + b.size ≤ _
    omega
  · simpa [commas] using fieldAppends.items_cons ba

 theorem Spec.object (good : FieldSpec writes values bound)
    (keysNodup : (values.map Prod.fst).Nodup) :
    Spec (Summary.object writes) (Json.mkObj values) (bound + 2) := by
  obtain ⟨bytes, meaning, size, appended⟩ := good
  refine ⟨"{".toUTF8 ++ bytes ++ "}".toUTF8, .object meaning keysNodup, ?_, ?_⟩
  · simp only [ByteArray.size_append]
    change 1 + bytes.size + 1 ≤ bound + 2
    omega
  · have joined := (Appends.text "{").seq (appended.seq (Appends.text "}"))
    simpa [Summary.object, ByteArray.append_assoc] using joined

end ANL.Boot.Reference.Summary
