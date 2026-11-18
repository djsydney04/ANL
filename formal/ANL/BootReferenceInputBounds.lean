import ANL.BootReferenceInputProofs

namespace ANL.Boot.Reference
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session

 theorem termNodes_positive (term : ANL.Words.Term) : 0 < termNodes term := by
  cases term <;> simp only [termNodes] <;> omega

 theorem boundedArray_iff : boundedArray j bound message = .ok values ↔
    ANL.Words.Wire.array j = .ok values ∧ values.size ≤ bound := by
  unfold boundedArray
  cases raw : ANL.Words.Wire.array j with
  | error e => simp [bind, Except.bind]
  | ok actual =>
    simp only [bind, Except.bind]
    by_cases over : actual.size > bound
    · simp only [over, ↓reduceIte]
      change (Except.error (limit message) : Decode (Array Json)) = .ok values ↔
        Except.ok actual = Except.ok values ∧ values.size ≤ bound
      simp only [reduceCtorEq, Except.ok.injEq]
      constructor
      · exact False.elim
      · rintro ⟨rfl, h⟩; omega
    · simp only [over, ↓reduceIte]
      change (Except.ok actual : Decode (Array Json)) = .ok values ↔
        Except.ok actual = Except.ok values ∧ values.size ≤ bound
      simp only [Except.ok.injEq]
      exact ⟨fun h => ⟨h, h ▸ Nat.le_of_not_gt over⟩, fun h => h.1⟩

 theorem array_limit_before_elements (array : ANL.Words.Wire.array j = .ok values)
    (over : bound < values.size) : boundedArray j bound message = .error (limit message) := by
  simp only [boundedArray, array, bind, Except.bind, over, ↓reduceIte]
  rfl

 theorem readByte_iff : readByte j = .ok value ↔
    ANL.Words.Wire.nat j = .ok value ∧ value < byteModulus := by
  unfold readByte
  cases raw : ANL.Words.Wire.nat j with
  | error e => simp [bind, Except.bind]
  | ok n =>
    simp only [bind, Except.bind]
    by_cases bad : n ≥ byteModulus
    · simp only [bad, ↓reduceIte]
      change (Except.error (invalid "reference read is not a byte") : Decode Nat) = .ok value ↔
        Except.ok n = Except.ok value ∧ value < byteModulus
      simp only [reduceCtorEq, Except.ok.injEq]
      constructor
      · exact False.elim
      · rintro ⟨rfl, h⟩; omega
    · simp only [bad, ↓reduceIte]
      change (Except.ok n : Decode Nat) = .ok value ↔
        Except.ok n = Except.ok value ∧ value < byteModulus
      simp only [Except.ok.injEq]
      exact ⟨fun h => ⟨h, h ▸ Nat.lt_of_not_ge bad⟩, fun h => h.1⟩

 theorem request_byte_failure (over : requestByteLimit < text.utf8ByteSize) :
    readRequest text = .error (limit "reference request byte limit") := by
  simp only [readRequest, over, ↓reduceIte]
  rfl

 theorem readRequest_byte_bound (read : readRequest text = .ok request) : text.utf8ByteSize ≤ requestByteLimit := by
  by_cases bound : text.utf8ByteSize ≤ requestByteLimit
  · exact bound
  · have failure := request_byte_failure (Nat.lt_of_not_ge bound)
    rw [failure] at read
    contradiction

 theorem readRequest_depth_guard (read : readRequest text = .ok request) : requestDepth text.toUTF8 = .ok () := by
  have bytes := readRequest_byte_bound read
  simp only [readRequest, Nat.not_lt.mpr bytes, ↓reduceIte] at read
  cases depth : requestDepth text.toUTF8 with
  | error e => simp only [depth, bind, Except.bind] at read; contradiction
  | ok value => cases value; rfl

 theorem checked_request_bytes (checked : checkDocuments coreText requestText = .ok input) :
    requestText.utf8ByteSize ≤ requestByteLimit ∧ requestDepth requestText.toUTF8 = .ok () :=
  ⟨readRequest_byte_bound (checkDocuments_iff.mp checked).2.2.1,
    readRequest_depth_guard (checkDocuments_iff.mp checked).2.2.1⟩

 theorem RequestValid.ordinal_range (valid : RequestValid p request)
    (delivery : request.environment.delivery = some d)
    (key : d.landmark = .beforePrimitive ordinal ident ∨ d.landmark = .afterPrimitive ordinal ident) :
    0 < ordinal ∧ ordinal ≤ wireNatMax ∧ ident ≤ wireNatMax := by
  have form := valid.scalars.delivery d delivery
  rcases key with h | h <;> simpa [LandmarkForm, h] using form

 theorem RequestValid.scoped (valid : RequestValid p request)
    (delivery : request.environment.delivery = some d) : Scoped p d.landmark :=
  (valid.input.delivery d delivery).scope

 theorem RequestValid.nonempty (valid : RequestValid p request) : request.actions ≠ [] := by
  obtain ⟨budget, rest, eq, _⟩ := valid.shape
  simp [eq]

 theorem checked_session_calls (checked : checkDocuments coreText requestText = .ok input)
    (calls : GatewayCalls input.program input.request.environment input.request.actions result observations ticks) :
    observations ≤ 65632 ∧ ticks ≤ 65536 := by
  cases result with
  | malformedShape =>
    have zero := calls.prestart_zero (.inl rfl)
    omega
  | invalidStart =>
    have zero := calls.prestart_zero (.inr rfl)
    omega
  | ran r =>
    have bounds := calls.poststart_counts
    have caps := checked_budget_bounds checked
    omega

end ANL.Boot.Reference
