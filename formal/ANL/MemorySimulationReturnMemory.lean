import ANL.MemorySimulationMemoryPhases

namespace ANL.Memory.Simulation
open Lowering

theorem return_readIndex
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.readIndex (resource := resource) (index := input) (rid := rid) code) before after a b)
    (atResult : AtResult b v (.captured input (.next d (.bufferRead rid input) tail) mk) ctrl actualKont) :
    Matched p q responses ⟨.ret v, a, .readIndex resource :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      ⟨.readCheck resource v, a, k, w⟩ := by
  cases atResult with
  | captured found =>
      have resourceFound : b.resource rid = some (binding resource) := placed.storage.2.2.1.head
      have facts := code.store_facts placed.storage.2.2.2
      have destination : Placed p (KontCode.destination code) before after a b :=
        ⟨placed.range, ⟨facts.1, facts.2.1, facts.2.2, placed.storage.2.2.2⟩,
          placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
      exact Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.readFound resourceFound found) .zero))
        (by decide) (Related.readCheck (KontCode.destination code) destination)

theorem return_writeIndex
    (lowered : term offset locals ids value start = some (fragment, nextSupply))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.writeIndex (resource := resource) (index := input) (rid := rid) lowered code) before after a b)
    (atResult : AtResult b v (.captured input (.next d (.bufferWrite rid input fragment.block) tail) mk) ctrl actualKont)
    (permission : resource.mode.CanWrite) :
    Matched p q responses ⟨.ret v, a, .writeIndex resource value :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      ⟨.writeCheck resource v value, a, k, w⟩ := by
  cases atResult with
  | captured found =>
      have resourceFound : b.resource rid = some (binding resource) := placed.storage.2.2.1.head
      have facts := code.store_facts placed.storage.2.2.2
      have le := placed.range.trans placed.limits.1
      have destination : Placed p (KontCode.destination code) before nextSupply a b :=
        ⟨le.trans (term_supply lowered), ⟨facts.1, facts.2.1, facts.2.2, placed.storage.2.2.2⟩,
          placed.limits.2, placed.offsets, placed.sites.2, placed.currentOffset⟩
      exact Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.writeFound resourceFound found permission) .zero))
        (by decide) (Related.writeCheck (KontCode.destination code) lowered le placed.sites.1 destination)

theorem return_writeValue
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p (KontCode.writeValue (resource := resource) (index := index) code) before after a b)
    (atResult : AtResult b (.scalar (.int value)) (.returned (.writeValue (binding resource) index :: mk)) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar (.int value)), a, .writeValue resource index :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      ⟨.store resource index value, a, k, w⟩ := by
  cases atResult
  have parent : Placed p code before after a b :=
    ⟨placed.range, placed.storage.2.2.2, placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
  exact Matched.positive (.succ Mir.Step.writeValueReturn .zero) (by decide) (.store code parent)

theorem return_owner
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p (KontCode.owner (rid := rid) (resource := resource) (site := site) code) before after a b)
    (atResult : AtResult b value (.returned (.owner rid (binding resource) site :: mk)) ctrl actualKont) :
    Matched p q responses ⟨.ret value, a, .owner resource site :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      ⟨.close resource site value, a, .owner resource site :: k, w⟩ := by
  cases atResult
  exact Matched.positive (.succ Mir.Step.ownerReturn .zero) (by decide)
    (Related.close (KontCode.owner code) placed)

theorem return_heapLength
    (initialLowered : term offset locals ids initializer start = some (initialCode, second))
    (yesLowered : term offset locals ((site.heap + offset) :: ids) yes second = some (yesCode, third))
    (noLowered : term offset locals ids no third = some (noCode, nextSupply))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.heapLength (length := input) initialLowered yesLowered noLowered code) before after a b)
    (atResult : AtResult b value (.captured input (.next d
      (.heapScope site.heap (site.heap + offset) input initialCode.block yesCode.block noCode.block) tail) mk) ctrl actualKont)
    (siteFunction : site.function = a.function) :
    Matched p q responses ⟨.ret value, a, .heapLength site initializer yes no :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      ⟨.lengthReady site value initializer yes no, a, k, w⟩ := by
  cases atResult with
  | captured found =>
      have facts := code.store_facts placed.storage.2.2.2
      have sameSite : Site.mk b.function site.heap = site := by
        cases site
        congr 1
        exact (siteFunction.trans facts.1.function).symm
      have le := placed.range.trans placed.limits.1
      have destination : Placed p (KontCode.destination code) before nextSupply a b :=
        ⟨((le.trans (term_supply initialLowered)).trans (term_supply yesLowered)).trans (term_supply noLowered),
          placed.storage, placed.limits.2, placed.offsets, placed.sites.2.2.2.2, placed.currentOffset⟩
      have related := Related.lengthReady (w := w) (value := value) (KontCode.destination code)
        initialLowered yesLowered noLowered le placed.sites.1 placed.sites.2.1 placed.sites.2.2.1
        placed.sites.2.2.2.1 destination
      apply Matched.positive (count := 2) (targetNext := _) ?_ (by decide) related
      refine MirStepsN.succ Mir.Step.instruction (MirStepsN.succ ?_ .zero)
      simpa only [sameSite] using
        (Mir.Step.heapFound (p := q) (responses := responses) (site := site.heap) (owner := site.heap + offset)
          (init := initialCode.block) (yes := yesCode.block) (no := noCode.block)
          (k := .instruction d tail :: mk) (w := w) found)

theorem return_heapInitial
    (yesLowered : term offset locals ((site.heap + offset) :: ids) yes start = some (yesCode, middle))
    (noLowered : term offset locals ids no middle = some (noCode, nextSupply))
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p (KontCode.heapInitial (length := length) yesLowered noLowered code) before after a b)
    (atResult : AtResult b (.scalar (.int value))
      (.returned (.heapInitial site (site.heap + offset) length yesCode.block noCode.block :: mk)) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar (.int value)), a, .heapInitial site length yes no :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      ⟨.allocate site length value yes no, a, k, w⟩ := by
  cases atResult
  have le := placed.range.trans placed.limits.1
  have parent : Placed p code before nextSupply a b :=
    ⟨(le.trans (term_supply yesLowered)).trans (term_supply noLowered), placed.storage.2.2.2,
      placed.limits.2, placed.offsets, placed.sites.2.2.2, placed.currentOffset⟩
  exact Matched.positive (.succ Mir.Step.heapInitialReturn .zero) (by decide)
    (Related.allocate code yesLowered noLowered le placed.sites.1 placed.sites.2.1 placed.sites.2.2.1 parent)

end ANL.Memory.Simulation
