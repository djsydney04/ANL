import ANL.BootRuntimeEffects

namespace ANL.Boot.Runtime
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem byteOperand_iff : byteOperand value = some n ↔ WordAt .w8 n value := by
  constructor
  · intro found
    cases value with
    | tuple _ => cases found
    | scalar scalar =>
      cases scalar with
      | legacy _ => cases found
      | word word =>
        rcases word with ⟨⟨width, m⟩, bound⟩
        cases width <;> simp [byteOperand] at found
        subst m
        exact .value bound
  · intro h; cases h; rfl

 theorem operationEffect_iff : operationEffect env h cursor op args = some result ↔
    OperationEffect env h cursor op args result := by
  constructor
  · intro found
    cases op <;> cases args with
    | nil =>
      simp only [operationEffect, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
      first
      | (rcases found with ⟨n, hn, v, hv, rfl⟩; exact .read hn (wordValue_iff.mp hv))
      | (subst result; first | exact .fence | exact .clear | exact .set | exact .install)
      | contradiction
    | cons value rest =>
      cases rest with
      | nil =>
        simp only [operationEffect, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
        first
        | (rcases found with ⟨n, hn, rfl⟩; exact .write (byteOperand_iff.mp hn))
        | contradiction
      | cons _ _ => cases found
  · intro meaning
    cases meaning with
    | read hn hv => simp [operationEffect, hn, wordValue_iff.mpr hv]
    | write hv => simp [operationEffect, byteOperand_iff.mpr hv]
    | fence => rfl
    | clear => rfl
    | set => rfl
    | install => rfl

 theorem perform_iff : perform p env h cursor op args = some result ↔ Effect p env h cursor op args result := by
  unfold perform
  split
  next valid =>
    rw [operationEffect_iff]
    exact ⟨fun effect => ⟨valid.1, valid.2, effect⟩, fun effect => effect.effect⟩
  next invalid =>
    constructor
    · intro bad; cases bad
    · intro effect; exact False.elim (invalid ⟨effect.hardware, effect.operation⟩)

 theorem Effect.deterministic (a : Effect p env h cursor op args x) (b : Effect p env h cursor op args y) : x = y :=
  Option.some.inj ((perform_iff.mpr a).symm.trans (perform_iff.mpr b))

 theorem ReadBlocked.no_effect (blocked : ReadBlocked p env h cursor op args) :
    ¬ Effect p env h cursor op args result := by
  rcases blocked with ⟨_, rfl, rfl, absent⟩
  intro effect
  cases effect.effect with | read found _ => simp [absent] at found

 theorem ReadBlocked.perform_none (blocked : ReadBlocked p env h cursor op args) :
    perform p env h cursor op args = none := by
  cases found : perform p env h cursor op args with
  | none => rfl
  | some result => exact False.elim (blocked.no_effect (perform_iff.mp found))

 theorem OperationEffect.result_type (effect : OperationEffect env h cursor op args result) :
    result.value.type = op.result := by
  cases effect with
  | read _ value => exact value.type
  | write _ => rfl
  | fence => rfl
  | clear => rfl
  | set => rfl
  | install => rfl

 theorem OperationEffect.arguments (effect : OperationEffect env h cursor op args result) :
    args.map Val.type = op.params := by
  cases effect with
  | write value => simp [value.type, Operation.params, byteTy]
  | _ => rfl

 theorem clear64_bound (bound : n < wordModulus) : clear64 n mask < wordModulus :=
  Nat.lt_of_le_of_lt Nat.and_le_left bound

 theorem write64_bound : write64 n < wordModulus := Nat.mod_lt _ (by decide)

 theorem Effect.hardware_valid (effect : Effect p env h cursor op args result) : result.hardware.Valid := by
  have valid := effect.hardware
  cases effect.effect <;> simp_all [Hardware.Valid, clear64_bound, write64_bound]

 theorem clear64_kernel (hn : n < wordModulus) (hm : mask < wordModulus) :
    ANL.Word.complement ⟨.w64, mask⟩ = .value ⟨.w64, wordModulus - 1 - mask⟩ ∧
    ANL.Word.binary .bitAnd ⟨.w64, n⟩ ⟨.w64, wordModulus - 1 - mask⟩ =
      .value ⟨.w64, clear64 n mask⟩ := by
  have complementBound : wordModulus - 1 - mask < wordModulus := by
    have positive : 0 < wordModulus := by decide
    omega
  constructor
  · simp [ANL.Word.complement, ANL.Word.Valid, hm]
  · simp [ANL.Word.binary, ANL.Word.Compatible, ANL.Word.Valid, hn, complementBound,
      ANL.Word.calculate, clear64]

 theorem Effect.cursor_change (effect : Effect p env h cursor op args result) :
    (∃ n, result.payload = .read n ∧ result.cursor = cursor + 1 ∧ env.reads[cursor]? = some n) ∨
      result.cursor = cursor := by
  cases effect.effect with
  | read found _ => exact .inl ⟨_, rfl, rfl, found⟩
  | _ => exact .inr rfl

 theorem Effect.read_exact (effect : Effect p env h cursor (.read8 region offset) args result) :
    args = [] ∧ ∃ n, env.reads[cursor]? = some n ∧ WordAt .w8 n result.value ∧
      result.payload = .read n ∧ result.hardware = h ∧ result.cursor = cursor + 1 := by
  cases effect.effect with | read found value => exact ⟨rfl, _, found, value, rfl, rfl, rfl⟩

 theorem Effect.write_exact (effect : Effect p env h cursor (.write8 region offset) args result) :
    ∃ n value, args = [value] ∧ WordAt .w8 n value ∧ result.payload = .write n ∧
      result.value = unitValue ∧ result.hardware = h ∧ result.cursor = cursor := by
  cases effect.effect with | write value => exact ⟨_, _, rfl, value, rfl, rfl, rfl, rfl⟩

 theorem commitState_retains :
    (commitState s pending result).machine = s.machine ∧
    (commitState s pending result).origins = s.origins ∧
    (commitState s pending result).nextOrdinal = s.nextOrdinal + 1 ∧
    (commitState s pending result).revEvents =
      .primitive pending.ordinal pending.declaration pending.operation result.payload :: s.revEvents ∧
    (commitState s pending result).phase = .primitiveAfter pending result.value ∧
    (commitState s pending result).deliveryUsed = s.deliveryUsed := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end ANL.Boot.Runtime
