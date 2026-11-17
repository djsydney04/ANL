import ANL.MemorySimulationContext

namespace ANL.Memory.Simulation
open Lowering

theorem return_arguments_cons
    (lowered : arguments offset locals ids (first :: remaining) start = some (out, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.arguments (f := functionId) (prior := prior)
      (current := current) (done := done) lowered code) before after a b)
    (atResult : AtResult b v (.captured current
      (plug out.instructions (.next d (.call functionId (done ++ current :: out.values)) tail)) mk) ctrl actualKont) :
    Matched p q responses ⟨.ret v, a, .arguments functionId none (first :: remaining) prior :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.eval first, a, .arguments functionId none remaining (v :: prior) :: k, w⟩ := by
  simp only [arguments, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨child, middle⟩, childLowered, ⟨rest, next⟩, restLowered, equality⟩ := lowered
  cases equality
  cases atResult with
  | captured found =>
      have le : SupplyLE before start := placed.range.trans placed.limits.1
      have facts := code.store_facts placed.storage.2.2.2
      have captured := Captured.append_value placed.storage.2.2.1.head found
      let continuation := KontCode.arguments (f := functionId) (prior := v :: prior)
        (current := child.value) (done := done ++ [current]) restLowered code
      have continued : Placed p continuation before middle a b :=
        ⟨le.trans (term_supply childLowered),
          ⟨facts.1, facts.2.1, CapturesHold.cons captured facts.2.2, placed.storage.2.2.2⟩,
          ⟨SupplyLE.refl _, placed.limits.2⟩, placed.offsets,
          ⟨fun e he => placed.sites.1 e (.tail _ he), placed.sites.2⟩, placed.currentOffset⟩
      apply Matched.silent CoreSilent.argumentReturn
      simpa only [beginArguments, plug_append, List.append_assoc, List.cons_append, List.nil_append] using
        Related.eval continuation childLowered (placed.sites.1 first (.head _))
          (continued.raise_before le (term_supply childLowered))

theorem return_arguments_nil
    (lowered : arguments offset locals ids [] start = some (out, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.arguments (f := functionId) (prior := prior)
      (current := current) (done := done) lowered code) before after a b)
    (atResult : AtResult b v (.captured current
      (plug out.instructions (.next d (.call functionId (done ++ current :: out.values)) tail)) mk) ctrl actualKont) :
    Matched p q responses ⟨.ret v, a, .arguments functionId none [] prior :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.invoke functionId none (v :: prior), a, k, w⟩ := by
  simp only [arguments, Option.some.injEq] at lowered
  cases lowered
  cases atResult with
  | captured found =>
      have facts := code.store_facts placed.storage.2.2.2
      have captured := Captured.append_value placed.storage.2.2.1.head found
      have destination : Placed p (KontCode.destination code) before start a b :=
        ⟨placed.range.trans placed.limits.1, ⟨facts.1, facts.2.1, facts.2.2, placed.storage.2.2.2⟩,
          placed.limits.2, placed.offsets, placed.sites.2, placed.currentOffset⟩
      apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.callFound captured) .zero)) (by decide)
      exact Related.invoke (KontCode.destination code) destination

theorem return_viewArguments_cons
    (lowered : arguments offset locals ids (first :: remaining) start = some (out, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.viewArguments (f := functionId) (sourceLoan := sourceLoan)
      (prior := prior) (current := current) (rid := rid) (done := done) lowered code) before after a b)
    (atResult : AtResult b v (.captured current
      (plug out.instructions (.next d (.callView functionId rid sourceLoan.mode
        (done ++ current :: out.values)) tail)) mk) ctrl actualKont) :
    Matched p q responses ⟨.ret v, a, .arguments functionId (some sourceLoan) (first :: remaining) prior :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩
      ⟨.eval first, a, .arguments functionId (some sourceLoan) remaining (v :: prior) :: k, w⟩ := by
  simp only [arguments, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨child, middle⟩, childLowered, ⟨rest, next⟩, restLowered, equality⟩ := lowered
  cases equality
  cases atResult with
  | captured found =>
      have le : SupplyLE before start := placed.range.trans placed.limits.1
      have facts := code.store_facts placed.storage.2.2.2
      have captured := Captured.append_value placed.storage.2.2.1.tail.head found
      let continuation := KontCode.viewArguments (f := functionId) (sourceLoan := sourceLoan)
        (prior := v :: prior) (current := child.value) (rid := rid) (done := done ++ [current]) restLowered code
      have continued : Placed p continuation before middle a b :=
        ⟨le.trans (term_supply childLowered),
          ⟨facts.1, facts.2.1, CapturesHold.cons placed.storage.2.2.1.head
            (CapturesHold.cons captured facts.2.2), placed.storage.2.2.2⟩,
          ⟨SupplyLE.refl _, placed.limits.2⟩, placed.offsets,
          ⟨fun e he => placed.sites.1 e (.tail _ he), placed.sites.2⟩, placed.currentOffset⟩
      apply Matched.silent CoreSilent.argumentReturn
      simpa only [beginArguments, plug_append, List.append_assoc, List.cons_append, List.nil_append] using
        Related.eval continuation childLowered (placed.sites.1 first (.head _))
          (continued.raise_before le (term_supply childLowered))

theorem return_viewArguments_nil
    (lowered : arguments offset locals ids [] start = some (out, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.viewArguments (f := functionId) (sourceLoan := sourceLoan)
      (prior := prior) (current := current) (rid := rid) (done := done) lowered code) before after a b)
    (atResult : AtResult b v (.captured current
      (plug out.instructions (.next d (.callView functionId rid sourceLoan.mode
        (done ++ current :: out.values)) tail)) mk) ctrl actualKont)
    (permission : sourceLoan.source.mode.CanLend sourceLoan.mode) :
    Matched p q responses ⟨.ret v, a, .arguments functionId (some sourceLoan) [] prior :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.invoke functionId (some sourceLoan) (v :: prior), a, k, w⟩ := by
  simp only [arguments, Option.some.injEq] at lowered
  cases lowered
  cases atResult with
  | captured found =>
      have facts := code.store_facts placed.storage.2.2.2
      have captured := Captured.append_value placed.storage.2.2.1.tail.head found
      have resource : b.resource rid = some (binding sourceLoan.source) := placed.storage.2.2.1.head
      have destination : Placed p (KontCode.destination code) before start a b :=
        ⟨placed.range.trans placed.limits.1, ⟨facts.1, facts.2.1, facts.2.2, placed.storage.2.2.2⟩,
          placed.limits.2, placed.offsets, placed.sites.2, placed.currentOffset⟩
      apply Matched.positive (.succ Mir.Step.instruction
        (.succ (Mir.Step.viewFound resource captured permission) .zero)) (by decide)
      exact Related.invoke (KontCode.destination code) destination

theorem return_fields_cons {prior : List APL.Val}
    (lowered : arguments offset locals ids (first :: remaining) start = some (out, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.fields (prior := prior) (current := current) (done := done) lowered code) before after a b)
    (atResult : AtResult b (.scalar v) (.captured current
      (plug out.instructions (.next d (.tuple (done ++ current :: out.values)) tail)) mk) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar v), a, .fields (first :: remaining) prior :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.eval first, a, .fields remaining (v :: prior) :: k, w⟩ := by
  simp only [arguments, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨child, middle⟩, childLowered, ⟨rest, next⟩, restLowered, equality⟩ := lowered
  cases equality
  cases atResult with
  | captured found =>
      have le : SupplyLE before start := placed.range.trans placed.limits.1
      have facts := code.store_facts placed.storage.2.2.2
      have captured := Captured.append_value placed.storage.2.2.1.head found
      let continuation := KontCode.fields (prior := v :: prior)
        (current := child.value) (done := done ++ [current]) restLowered code
      have continued : Placed p continuation before middle a b :=
        ⟨le.trans (term_supply childLowered),
          ⟨facts.1, facts.2.1, CapturesHold.cons captured facts.2.2, placed.storage.2.2.2⟩,
          ⟨SupplyLE.refl _, placed.limits.2⟩, placed.offsets,
          ⟨fun e he => placed.sites.1 e (.tail _ he), placed.sites.2⟩, placed.currentOffset⟩
      apply Matched.silent CoreSilent.fieldNext
      simpa only [plug_append, List.append_assoc, List.cons_append, List.nil_append] using
        Related.eval continuation childLowered (placed.sites.1 first (.head _))
          (continued.raise_before le (term_supply childLowered))

theorem return_fields_nil {prior : List APL.Val}
    (lowered : arguments offset locals ids [] start = some (out, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.fields (prior := prior) (current := current) (done := done) lowered code) before after a b)
    (atResult : AtResult b (.scalar v) (.captured current
      (plug out.instructions (.next d (.tuple (done ++ current :: out.values)) tail)) mk) ctrl actualKont)
    (valid : APL.FlatProducts.construct (v :: prior).reverse ≠ .invalid) :
    Matched p q responses ⟨.ret (.scalar v), a, .fields [] prior :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      (ANL.Memory.resume (APL.FlatProducts.construct (v :: prior).reverse) a k w) := by
  simp only [arguments, Option.some.injEq] at lowered
  cases lowered
  cases atResult with
  | captured found =>
      have facts := code.store_facts placed.storage.2.2.2
      have captured : b.capture (done ++ [current]) = some ((v :: prior).reverse.map APL.FlatProducts.Val.scalar) := by
        simpa only [Captured, List.map_cons, List.map_reverse] using
          Captured.append_value placed.storage.2.2.1.head found
      have destination : Placed p (KontCode.destination code) before start a b :=
        ⟨placed.range.trans placed.limits.1, ⟨facts.1, facts.2.1, facts.2.2, placed.storage.2.2.2⟩,
          placed.limits.2, placed.offsets, placed.sites.2, placed.currentOffset⟩
      apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.tupleFound captured) .zero)) (by decide)
      simpa only [constructTuple_map] using resume_related destination valid

end ANL.Memory.Simulation
