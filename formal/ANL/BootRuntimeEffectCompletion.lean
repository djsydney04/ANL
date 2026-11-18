import ANL.BootRuntimeInterceptionBoundary

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program}

 theorem byte_typed (typed : value.type = byteTy) : ∃ n, WordAt .w8 n value := by
  cases value with
  | tuple _ => cases typed
  | scalar scalar =>
    cases scalar with
    | legacy value => cases value <;> cases typed
    | word value =>
      rcases value with ⟨⟨width, n⟩, bound⟩
      cases width <;> cases typed
      exact ⟨n, .value bound⟩

 theorem typed_write_arguments (typed : args.map Val.type = [byteTy]) :
    ∃ n value, args = [value] ∧ WordAt .w8 n value := by
  cases args with
  | nil => cases typed
  | cons value rest =>
    simp only [List.map_cons, List.cons.injEq] at typed
    have empty : rest = [] := List.map_eq_nil_iff.mp typed.2
    subst rest
    obtain ⟨n, word⟩ := byte_typed typed.1
    exact ⟨n, value, rfl, word⟩

/-- Missing input is the only obstruction to a typed permitted transaction. -/
 theorem effect_or_read_block (input : InputValid p env) (hardware : h.Valid)
    (allowed : op.Valid p.entries.hardware.function) (typed : args.map Val.type = op.params) :
    (∃ result, Effect p env h cursor op args result) ∨ ReadBlocked p env h cursor op args := by
  cases allowed with
  | read8 =>
    have empty : args = [] := List.map_eq_nil_iff.mp typed
    subst args
    cases found : env.reads[cursor]? with
    | none => exact .inr ⟨hardware, rfl, rfl, found⟩
    | some n => exact .inl ⟨_, ⟨hardware, .read8, .read found (.value (input.read_bound found))⟩⟩
  | write8 offset =>
    obtain ⟨n, value, rfl, word⟩ := typed_write_arguments typed
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

 theorem pending_effect_or_block (input : InputValid p env) (old : RuntimeInvariant p env s)
    (pending : PendingAt p s q) :
    (∃ result, Effect p env s.hardware s.readCursor q.operation q.arguments result) ∨
      ReadBlocked p env s.hardware s.readCursor q.operation q.arguments :=
  effect_or_read_block input old.hardware pending.2.2.2.1 pending.2.2.2.2.1

end ANL.Boot.Runtime
