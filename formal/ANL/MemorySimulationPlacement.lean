import ANL.MemorySimulationLimits

namespace ANL.Memory.Simulation
open Lowering

variable {mk : List Mir.Frame}

theorem Placed.raise_before (h : Placed p code before after source target)
    (le : SupplyLE before middle) (hi : SupplyLE middle after) :
    Placed p code middle after source target :=
  ⟨hi, code.store_weaken h.storage le, h.limits, h.offsets, h.sites, h.currentOffset⟩

def Placed.snapshot {code : KontCode offset locals ids k result captures}
    (h : Placed p code before after source target) : SavedTemps locals :=
  ⟨target.temps, before, (code.store_facts h.storage).2.1.temps,
    below_local (code.store_facts h.storage).1.values (code.store_facts h.storage).2.1⟩

theorem Placed.blockEnd {code : KontCode offset locals ids k (.returned mk) captures}
    (h : Placed p code before after source target) :
    Placed p (KontCode.blockEnd h.snapshot code) before after source target := by
  have facts := code.store_facts h.storage
  refine ⟨h.range, ⟨facts.1, facts.2.1, facts.2.2, ?_, SupplyLE.refl _, h.storage⟩,
    ⟨h.range, code.limits_rebase h.storage h.limits h.range⟩, h.offsets, h.sites, h.currentOffset⟩
  intro rid _
  rfl

theorem Placed.blockEnd_at {code : KontCode offset locals ids k (.returned mk) captures}
    (h : Placed p code before after source target) (le : SupplyLE before next) :
    Placed p (KontCode.blockEnd h.snapshot code) before next source target := by
  have facts := code.store_facts h.storage
  refine ⟨le, ⟨facts.1, facts.2.1, facts.2.2, ?_, SupplyLE.refl _, h.storage⟩,
    ⟨le, code.limits_rebase h.storage h.limits h.range⟩, h.offsets, h.sites, h.currentOffset⟩
  intro rid _
  rfl

theorem Placed.yield {code : KontCode offset locals ids k (.returned mk) captures}
    (h : Placed p code before after source target) :
    Placed p (KontCode.yield (value := value) code) before after source target := by
  have facts := code.store_facts h.storage
  exact ⟨h.range, ⟨facts.1, facts.2.1, facts.2.2, h.storage⟩,
    h.limits, h.offsets, h.sites, h.currentOffset⟩

theorem Placed.destination {code : KontCode offset locals ids k (.captured d tail mk) captures}
    (h : Placed p code before (afterTemp middle d) source target)
    (le : SupplyLE before middle) (fresh : middle.nextTemp ≤ d.id) :
    Placed p (KontCode.destination code) before middle source target := by
  have facts := code.store_facts h.storage
  exact ⟨le, ⟨facts.1, facts.2.1, facts.2.2, h.storage⟩,
    ⟨fresh, h.limits⟩, h.offsets, h.sites, h.currentOffset⟩

@[simp] theorem plug_nil : plug [] tail = tail := rfl
@[simp] theorem plug_cons : plug (instruction :: rest) tail =
    .next instruction.destination instruction.operation (plug rest tail) := rfl

theorem plug_append : plug (left ++ right) tail = plug left (plug right tail) := by
  simp [plug, List.foldr_append]

@[simp] theorem plug_yield (fragment : Fragment) :
    plug fragment.instructions (.yield fragment.value) = fragment.block := by
  rfl

/-- Enter the actual nested MIR block, saving only its currently visible Temps. -/
theorem enter_block {code : KontCode offset locals ids k (.returned mk) captures}
    (h : Placed p code before after source target)
    (lowered : term offset locals ids e start = some (fragment, next))
    (le : SupplyLE before start) (sites : ScopedSites offset ids e) :
    ∃ last, MirStepsN q responses 1 ⟨.block fragment.block, target, mk, world⟩ last ∧
      Related p ⟨.eval e, source, k, world⟩ last := by
  refine ⟨_, .succ Mir.Step.block .zero, ?_⟩
  have placed := (h.blockEnd_at (le.trans (term_supply lowered))).yield (value := fragment.value)
  have moved := placed.raise_before le (term_supply lowered)
  have related := Related.eval (w := world) (KontCode.yield (KontCode.blockEnd h.snapshot code)) lowered sites moved
  simpa only [plug_yield, Placed.snapshot] using related

end ANL.Memory.Simulation
