import ANL.BootV2RuntimeEffects
import ANL.BootRuntimeEffectCompletion

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (Hardware EffectResult OperationEffect operationEffect operationEffect_iff
  Pending WordAt unitValue clear64_bound write64_bound)
variable {p : ANL.Boot.V2.Program} {op : ANL.Boot.Operation} {h : Hardware} {cursor : Nat}
set_option linter.unusedSimpArgs false

theorem performLegacy_iff : performLegacy p env h cursor op args = some result ↔
    LegacyEffect p env h cursor op args result := by
  unfold performLegacy
  split
  next valid =>
    rw [operationEffect_iff]
    exact ⟨fun effect => ⟨valid.1, valid.2, effect⟩, fun effect => effect.effect⟩
  next invalid =>
    constructor
    · intro bad; cases bad
    · intro effect; exact False.elim (invalid ⟨effect.hardware, effect.operation⟩)

theorem LegacyEffect.deterministic (a : LegacyEffect p env h cursor op args x)
    (b : LegacyEffect p env h cursor op args y) : x = y :=
  Option.some.inj ((performLegacy_iff.mpr a).symm.trans (performLegacy_iff.mpr b))

theorem LegacyReadBlocked.no_effect (blocked : LegacyReadBlocked p env h cursor op args) :
    ¬ LegacyEffect p env h cursor op args result := by
  rcases blocked with ⟨_, rfl, rfl, absent⟩
  intro effect
  cases effect.effect with | read found _ => simp [absent] at found

theorem LegacyReadBlocked.perform_none (blocked : LegacyReadBlocked p env h cursor op args) :
    performLegacy p env h cursor op args = none := by
  cases found : performLegacy p env h cursor op args with
  | none => rfl
  | some result => exact False.elim (blocked.no_effect (performLegacy_iff.mp found))

theorem LegacyEffect.result_type (effect : LegacyEffect p env h cursor op args result) :
    result.value.type = op.result := effect.effect.result_type

theorem LegacyEffect.arguments (effect : LegacyEffect p env h cursor op args result) :
    args.map Val.type = op.params := effect.effect.arguments

theorem LegacyEffect.hardware_valid (effect : LegacyEffect p env h cursor op args result) :
    result.hardware.Valid := by
  have valid := effect.hardware
  cases effect.effect <;> simp_all [Hardware.Valid, clear64_bound, write64_bound]

theorem LegacyEffect.cursor_change (effect : LegacyEffect p env h cursor op args result) :
    (∃ n, result.payload = .read n ∧ result.cursor = cursor + 1 ∧ env.legacy.reads[cursor]? = some n) ∨
      result.cursor = cursor := by
  cases effect.effect with
  | read found _ => exact .inl ⟨_, rfl, rfl, found⟩
  | _ => exact .inr rfl

theorem LegacyEffect.read_exact (effect : LegacyEffect p env h cursor (.read8 region offset) args result) :
    args = [] ∧ ∃ n, env.legacy.reads[cursor]? = some n ∧ WordAt .w8 n result.value ∧
      result.payload = .read n ∧ result.hardware = h ∧ result.cursor = cursor + 1 := by
  cases effect.effect with | read found value => exact ⟨rfl, _, found, value, rfl, rfl, rfl⟩

theorem LegacyEffect.write_exact (effect : LegacyEffect p env h cursor (.write8 region offset) args result) :
    ∃ n value, args = [value] ∧ WordAt .w8 n value ∧ result.payload = .write n ∧
      result.value = unitValue ∧ result.hardware = h ∧ result.cursor = cursor := by
  cases effect.effect with | write value => exact ⟨_, _, rfl, value, rfl, rfl, rfl, rfl⟩

theorem LegacyEffect.installed (effect : LegacyEffect p env h cursor op args result)
    (installed : h.installedHandler = none ∨ h.installedHandler = some p.entries.hardware.function) :
    result.hardware.installedHandler = none ∨ result.hardware.installedHandler = some p.entries.hardware.function := by
  have policy := effect.operation
  cases effect.effect
  all_goals first | exact installed | (cases policy; exact .inr rfl)

theorem LegacyEffect.cursor_bound (effect : LegacyEffect p env h cursor op args result)
    (bound : cursor ≤ env.legacy.reads.length) : result.cursor ≤ env.legacy.reads.length := by
  rcases effect.cursor_change with ⟨n, _, increment, found⟩ | same
  · have within := (List.getElem?_eq_some_iff.mp found).1
    omega
  · omega

theorem legacy_effect_or_read_block (input : InputValid p env) (hardware : h.Valid)
    (allowed : op.Valid p.entries.hardware.function) (typed : args.map Val.type = op.params) :
    (∃ result, LegacyEffect p env h cursor op args result) ∨
      LegacyReadBlocked p env h cursor op args := by
  cases allowed with
  | read8 =>
    have empty : args = [] := List.map_eq_nil_iff.mp typed
    subst args
    cases found : env.legacy.reads[cursor]? with
    | none => exact .inr ⟨hardware, rfl, rfl, found⟩
    | some n => exact .inl ⟨_, ⟨hardware, .read8, .read found (.value (input.read_bound found))⟩⟩
  | write8 offset =>
    obtain ⟨n, value, rfl, word⟩ := ANL.Boot.Runtime.typed_write_arguments typed
    exact .inl ⟨_, ⟨hardware, .write8 offset, .write word⟩⟩
  | fence =>
    have empty : args = [] := List.map_eq_nil_iff.mp typed
    subst args
    exact .inl ⟨_, ⟨hardware, .fence, .fence⟩⟩
  | csrClear =>
    have empty : args = [] := List.map_eq_nil_iff.mp typed
    subst args
    exact .inl ⟨_, ⟨hardware, .csrClear, .clear⟩⟩
  | csrWrite =>
    have empty : args = [] := List.map_eq_nil_iff.mp typed
    subst args
    exact .inl ⟨_, ⟨hardware, .csrWrite, .set⟩⟩
  | installTrap =>
    have empty : args = [] := List.map_eq_nil_iff.mp typed
    subst args
    exact .inl ⟨_, ⟨hardware, .installTrap, .install⟩⟩

theorem commitLegacyState_retains :
    (commitLegacyState s pending result).machine = s.machine ∧
    (commitLegacyState s pending result).origins = s.origins ∧
    (commitLegacyState s pending result).nextOrdinal = s.nextOrdinal + 1 ∧
    (commitLegacyState s pending result).revEvents =
      .legacy (.primitive pending.ordinal pending.declaration pending.operation result.payload) :: s.revEvents ∧
    (commitLegacyState s pending result).phase = .legacy (.primitiveAfter pending result.value) ∧
    (commitLegacyState s pending result).deliveryUsed = s.deliveryUsed ∧
    (commitLegacyState s pending result).forwardingUsed = s.forwardingUsed ∧
    (commitLegacyState s pending result).interrupted = s.interrupted :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ANL.Boot.V2.Runtime
