import ANL.MemorySimulationValues
import ANL.MemorySimulationKontInvariant

namespace ANL.Memory.Simulation
open Lowering

@[refl] theorem SupplyLE.refl (s : Supply) : SupplyLE s s := ⟨Nat.le_refl _, Nat.le_refl _⟩
theorem SupplyLE.trans (h : SupplyLE a b) (g : SupplyLE b c) : SupplyLE a c :=
  ⟨Nat.le_trans h.1 g.1, Nat.le_trans h.2 g.2⟩

theorem Below.weaken (h : Below a state) (le : SupplyLE a b) : Below b state :=
  ⟨fun id v hv => Nat.lt_of_lt_of_le (h.temps id v hv) le.1,
    fun id v hv => Nat.lt_of_lt_of_le (h.slots id v hv) le.2⟩

theorem below_local (h : LocalsRel target locals values) (hb : Below supply target) :
    LocalsBelow supply locals := by
  intro l hl
  obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp hl
  obtain ⟨v, _, hv⟩ := h.lookup hi
  cases l with
  | value temp => exact hb.temps _ _ (lookupId_mem hv)
  | mutable slot => exact hb.slots _ _ (lookupId_mem hv)

private theorem counts_monotone {before after : Nat} {counts : Nat → Nat}
    (h : ∀ id, counts id + (List.range before).count id = (List.range after).count id) : before ≤ after := by
  by_cases hn : before ≤ after
  · exact hn
  · have hb : after < before := by omega
    have eq := h after
    simp [List.count_range, hb] at eq

theorem term_supply (lowered : term offset locals resources e before = some (fragment, after)) :
    SupplyLE before after := by
  have effect := InventoryProof.term_effect e offset locals resources before after fragment lowered
  exact ⟨counts_monotone effect.temps, counts_monotone effect.slots⟩

theorem arguments_supply
    (lowered : arguments offset locals resources args before = some (fragment, after)) :
    SupplyLE before after := by
  induction args generalizing before after fragment with
  | nil =>
      simp only [arguments, Option.some.injEq] at lowered
      cases lowered
      exact .refl _
  | cons head tail ih =>
      simp only [arguments, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨fh, s1⟩, hh, ⟨ft, s2⟩, ht, lowered⟩ := lowered
      cases lowered
      exact (term_supply hh).trans (ih ht)

end ANL.Memory.Simulation
