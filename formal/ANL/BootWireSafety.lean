import ANL.BootWire
import ANL.BootCarrier
import ANL.BootTableProofs

namespace ANL.Boot.Wire

theorem checkCoreDocument_iff {text : String} {p : Program} :
    checkCoreDocument text = .ok p ↔ readCore text = .ok p ∧ WellFormedProgram p := by
  unfold checkCoreDocument
  cases hr : readCore text with
  | error e => simp [bind, Except.bind]
  | ok c =>
    simp only [bind, Except.bind]
    split
    · rename_i hc
      simp only [pure, Except.pure, Except.ok.injEq]
      constructor
      · intro h; subst c; exact ⟨rfl, checkProgram_iff.mp hc⟩
      · intro h; exact h.1
    · rename_i hc
      constructor
      · intro h; cases h
      · rintro ⟨h, hp⟩
        cases h
        exact False.elim (hc (checkProgram_iff.mpr hp))

theorem checked_wellFormed {text : String} {p : Program}
    (checked : checkCoreDocument text = .ok p) : WellFormedProgram p :=
  (checkCoreDocument_iff.mp checked).2

variable {text : String} {p : Program} (checked : checkCoreDocument text = .ok p)
include checked

theorem checked_metadata : MetadataValid p := (checked_wellFormed checked).metadata

theorem checked_roles : RolesValid p := (checked_wellFormed checked).roles

theorem checked_memoryFree {f : Nat} {d : Defined}
    (found : p.functions[f]? = some (.defined d)) : MemoryFree d.function.body :=
  (checked_wellFormed checked).memoryFree found

theorem checked_no_view {f : Nat} {d : Defined}
    (found : p.functions[f]? = some (.defined d)) : d.function.view = none :=
  (checked_wellFormed checked).no_view found

/-- The boot prefix alone has machine authority; FunctionPolicy checks the rest. -/
theorem checked_effect_policy {f : Nat} {d : Defined}
    (found : p.functions[f]? = some (.defined d)) :
    EffectSetValid p d ∧ FunctionPolicy p d :=
  ⟨((checked_wellFormed checked).at found).effects,
    ((checked_wellFormed checked).at found).policy⟩

theorem checked_call_target {f g : Nat} {d : Defined}
    (found : p.functions[g]? = some (.defined d)) (mem : f ∈ calls d.function.body) :
    f < p.functions.length ∧ f ∉ p.roleIDs :=
  (checked_wellFormed checked).call_target found mem

theorem checked_no_synthetic_call {f : Nat} {d : Defined}
    (found : p.functions[f]? = some (.defined d)) :
    p.functions.length ∉ calls d.function.body :=
  (checked_wellFormed checked).no_synthetic_call found

theorem checked_cycleFree : CycleFree p := (checked_wellFormed checked).no_cycles

theorem checked_discovery : FirstUses p.operationUses (p.primitives.map Primitive.operation) :=
  (checked_wellFormed checked).discovery

theorem checked_primitive_keys_unique : (p.primitives.map Primitive.operation).Nodup :=
  (checked_wellFormed checked).primitive_keys_unique

theorem checked_primitive_id {i : Nat} {d : Primitive}
    (found : p.primitives[i]? = some d) : d.id = p.defined.length + i :=
  (checked_wellFormed checked).primitive_id found

theorem checked_primitive_bound : p.primitives.length ≤ 10 :=
  (checked_wellFormed checked).at_most_ten_primitives

/-- This proves the static adapter only; the probe never exports or executes it. -/
theorem checked_carrier_typed : ANL.Words.WellFormedProgram p.carrier :=
  carrier_wellFormed (checked_wellFormed checked)

end ANL.Boot.Wire
