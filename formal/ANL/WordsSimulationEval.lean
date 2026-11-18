import ANL.WordsSimulationContext
import ANL.WordsSimulationSites

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

theorem eval_lit
    (lowered : term offset locals ids (.lit ty literal) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b) :
    Matched p q responses ⟨.eval (.lit ty literal), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩ ⟨.ret (.scalar (.legacy literal)), a, k, w⟩ := by
  simp only [term, Option.some.injEq] at lowered
  cases lowered
  have dest := placed.destination (middle := before) (SupplyLE.refl _) (Nat.le_refl _)
  cases literal with
  | int n =>
      apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.integer (n := n)) .zero)) (by decide)
      exact Related.ret (KontCode.destination code) dest .returned
  | bool v =>
      apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.boolean (v := v)) .zero)) (by decide)
      exact Related.ret (KontCode.destination code) dest .returned
  | unit =>
      apply Matched.positive (.succ Mir.Step.instruction (.succ Mir.Step.unit .zero)) (by decide)
      exact Related.ret (KontCode.destination code) dest .returned

theorem eval_word
    (lowered : term offset locals ids (.word ty width payload) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b)
    (valid : wordLiteral width payload ≠ .invalid) :
    Matched p q responses ⟨.eval (.word ty width payload), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      (resume (wordLiteral width payload) a k w) := by
  simp only [term, Option.some.injEq] at lowered
  cases lowered
  have dest := placed.destination (middle := before) (SupplyLE.refl _) (Nat.le_refl _)
  apply Matched.positive (.succ Mir.Step.instruction (.succ Mir.Step.word .zero)) (by decide)
  exact resume_related dest valid

theorem eval_local
    (lowered : term offset locals ids (.local ty index) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b) (found : a.env[index]? = some v) :
    Matched p q responses ⟨.eval (.local ty index), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩ ⟨.ret v, a, k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff] at lowered
  obtain ⟨entry, lookup, lowered⟩ := lowered
  have facts := code.store_facts placed.storage
  obtain ⟨prior, sourceLookup, targetLookup⟩ := facts.1.values.lookup lookup
  have same : prior = v := Option.some.inj (sourceLookup.symm.trans found)
  subst prior
  cases entry with
  | value temp =>
      simp only [Option.pure_def, Option.some.injEq] at lowered
      cases lowered
      exact Matched.silent (.localFound found) (.ret code placed (.captured targetLookup))
  | mutable slot =>
      simp only [Option.pure_def, Option.some.injEq] at lowered
      cases lowered
      have dest := placed.destination (middle := before) (SupplyLE.refl _) (Nat.le_refl _)
      apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.loadFound targetLookup) .zero)) (by decide)
      exact Related.ret (KontCode.destination code) dest .returned

theorem eval_convert
    (lowered : term offset locals ids (.convert ty mode target operand) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b) (sites : ScopedSites offset ids operand) :
    Matched p q responses ⟨.eval (.convert ty mode target operand), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval operand, a, .convert mode target :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨child, middle⟩, childLowered, equality⟩ := lowered
  cases equality
  let continuation := KontCode.convert (mode := mode) (target := target) (value := child.value) code
  have facts := code.store_facts placed.storage
  have nextPlaced : Placed p continuation before middle a b :=
    ⟨term_supply childLowered, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
      ⟨Nat.le_refl _, placed.limits⟩, placed.offsets, placed.sites, placed.currentOffset⟩
  apply Matched.silent CoreSilent.convertEval
  simpa [emit, plug_append] using Related.eval (w := w) continuation childLowered sites nextPlaced

theorem eval_unary
    (lowered : term offset locals ids (.unary ty op operand) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b) (sites : ScopedSites offset ids operand) :
    Matched p q responses ⟨.eval (.unary ty op operand), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval operand, a, .unary op :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨child, middle⟩, childLowered, equality⟩ := lowered
  cases equality
  let continuation := KontCode.unary (op := op) (value := child.value) code
  have facts := code.store_facts placed.storage
  have nextPlaced : Placed p continuation before middle a b :=
    ⟨term_supply childLowered, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
      ⟨Nat.le_refl _, placed.limits⟩, placed.offsets, placed.sites, placed.currentOffset⟩
  apply Matched.silent CoreSilent.unaryEval
  simpa [emit, plug_append] using Related.eval (w := w) continuation childLowered sites nextPlaced

theorem eval_project
    (lowered : term offset locals ids (.project ty operand index) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b) (sites : ScopedSites offset ids operand) :
    Matched p q responses ⟨.eval (.project ty operand index), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval operand, a, .project index :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨child, middle⟩, childLowered, equality⟩ := lowered
  cases equality
  let continuation := KontCode.project (index := index) (value := child.value) code
  have facts := code.store_facts placed.storage
  have nextPlaced : Placed p continuation before middle a b :=
    ⟨term_supply childLowered, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
      ⟨Nat.le_refl _, placed.limits⟩, placed.offsets, placed.sites, placed.currentOffset⟩
  apply Matched.silent CoreSilent.projectEval
  simpa [emit, plug_append] using Related.eval (w := w) continuation childLowered sites nextPlaced

theorem eval_assign
    (lowered : term offset locals ids (.assign ty index operand) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b) (sites : ScopedSites offset ids operand) :
    Matched p q responses ⟨.eval (.assign ty index operand), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval operand, a, .assign index :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨entry, lookup, lowered⟩ := lowered
  cases entry with
  | value temp => simp at lowered
  | mutable slot =>
      simp only [Option.bind_eq_some_iff] at lowered
      obtain ⟨⟨child, middle⟩, childLowered, equality⟩ := lowered
      cases equality
      let continuation := KontCode.assign (value := child.value) lookup code
      have facts := code.store_facts placed.storage
      have nextPlaced : Placed p continuation before middle a b :=
        ⟨term_supply childLowered, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
          ⟨Nat.le_refl _, placed.limits⟩, placed.offsets, placed.sites, placed.currentOffset⟩
      apply Matched.silent CoreSilent.assignEval
      simpa [emit, plug_append] using Related.eval (w := w) continuation childLowered sites nextPlaced

theorem eval_let
    (lowered : term offset locals ids (.letE ty initializer body) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b)
    (sites : SiteList offset ids (initializer.heapSites ++ body.heapSites)) :
    Matched p q responses ⟨.eval (.letE ty initializer body), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval initializer, a, .bind false body :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨child, middle⟩, childLowered, ⟨bodyCode, next⟩, bodyLowered, equality⟩ := lowered
  cases equality
  let continuation := KontCode.bindValue bodyLowered code
  have facts := code.store_facts placed.storage
  have nextPlaced : Placed p continuation before middle a b :=
    ⟨term_supply childLowered, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
      ⟨SupplyLE.refl _, placed.limits⟩, placed.offsets, ⟨sites.append_right, placed.sites⟩,
      placed.currentOffset⟩
  apply Matched.silent CoreSilent.letEval
  simpa [Fragment.prefix, plug_append] using
    Related.eval (w := w) continuation childLowered sites.append_left nextPlaced

theorem eval_letMut
    (lowered : term offset locals ids (.letMut ty initializer body) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b)
    (sites : SiteList offset ids (initializer.heapSites ++ body.heapSites)) :
    Matched p q responses ⟨.eval (.letMut ty initializer body), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval initializer, a, .bind true body :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨child, middle⟩, childLowered, ⟨bodyCode, next⟩, bodyLowered, equality⟩ := lowered
  cases equality
  let continuation := KontCode.bindMutable (value := child.value) bodyLowered code
  have facts := code.store_facts placed.storage
  have nextPlaced : Placed p continuation before middle a b :=
    ⟨term_supply childLowered, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
      ⟨Nat.le_refl _, Nat.le_refl _, rfl, Nat.le_refl _, placed.limits⟩,
      placed.offsets, ⟨sites.append_right, placed.sites⟩, placed.currentOffset⟩
  apply Matched.silent CoreSilent.letMutEval
  simpa [emit, plug_append] using
    Related.eval (w := w) continuation childLowered sites.append_left nextPlaced

theorem eval_if
    (lowered : term offset locals ids (.ifE ty condition yes no) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b)
    (sites : SiteList offset ids (condition.heapSites ++ yes.heapSites ++ no.heapSites)) :
    Matched p q responses ⟨.eval (.ifE ty condition yes no), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval condition, a, .ifF yes no :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨child, middle⟩, childLowered, ⟨left, second⟩, leftLowered,
    ⟨right, next⟩, rightLowered, equality⟩ := lowered
  cases equality
  let continuation := KontCode.branch (condition := child.value) leftLowered rightLowered code
  have facts := code.store_facts placed.storage
  have nextPlaced : Placed p continuation before middle a b :=
    ⟨term_supply childLowered, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
      ⟨SupplyLE.refl _, Nat.le_refl _, placed.limits⟩, placed.offsets,
      ⟨sites.append_left.append_right, sites.append_right, placed.sites⟩, placed.currentOffset⟩
  apply Matched.silent CoreSilent.ifEval
  simpa [emit, plug_append] using
    Related.eval (w := w) continuation childLowered sites.append_left.append_left nextPlaced

theorem eval_while
    (lowered : term offset locals ids (.whileE ty condition body) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b)
    (sites : SiteList offset ids (condition.heapSites ++ body.heapSites)) :
    Matched p q responses ⟨.eval (.whileE ty condition body), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval condition, a, .condition condition body :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨cf, middle⟩, conditionLowered, ⟨bf, next⟩, bodyLowered, equality⟩ := lowered
  cases equality
  have dest := placed.destination ((term_supply conditionLowered).trans (term_supply bodyLowered)) (Nat.le_refl _)
  let continuation := KontCode.condition conditionLowered bodyLowered (KontCode.destination code)
  have facts := (KontCode.destination code).store_facts dest.storage
  have nextPlaced : Placed p continuation before before a b :=
    ⟨SupplyLE.refl _, ⟨facts.1, facts.2.1, facts.2.2, dest.storage⟩,
      ⟨SupplyLE.refl _, dest.limits⟩, dest.offsets,
      ⟨sites.append_left, sites.append_right, dest.sites⟩, dest.currentOffset⟩
  obtain ⟨last, path, related⟩ := enter_block (world := w) nextPlaced conditionLowered (SupplyLE.refl _) sites.append_left
  exact Matched.positive (.succ Mir.Step.instruction (.succ Mir.Step.whileStart path)) (by decide) related

theorem eval_binary
    (lowered : term offset locals ids (.binary ty op left right) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b)
    (sites : SiteList offset ids (left.heapSites ++ right.heapSites)) :
    Matched p q responses ⟨.eval (.binary ty op left right), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval left, a, .left op right :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨lf, middle⟩, leftLowered, lowered⟩ := lowered
  by_cases logical : op = (.legacy .and) ∨ op = (.legacy .or)
  · simp only [ite_eq_left logical, Option.bind_eq_some_iff] at lowered
    obtain ⟨⟨rf, next⟩, rightLowered, equality⟩ := lowered
    cases equality
    rcases logical with rfl | rfl
    · let continuation := KontCode.andLeft (left := lf.value) rightLowered code
      have facts := code.store_facts placed.storage
      have nextPlaced : Placed p continuation before middle a b :=
        ⟨term_supply leftLowered, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
          ⟨SupplyLE.refl _, Nat.le_refl _, placed.limits⟩, placed.offsets,
          ⟨sites.append_right, placed.sites⟩, placed.currentOffset⟩
      apply Matched.silent CoreSilent.binaryEval
      simpa [emit, plug_append] using
        Related.eval (w := w) continuation leftLowered sites.append_left nextPlaced
    · let continuation := KontCode.orLeft (left := lf.value) rightLowered code
      have facts := code.store_facts placed.storage
      have nextPlaced : Placed p continuation before middle a b :=
        ⟨term_supply leftLowered, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
          ⟨SupplyLE.refl _, Nat.le_refl _, placed.limits⟩, placed.offsets,
          ⟨sites.append_right, placed.sites⟩, placed.currentOffset⟩
      apply Matched.silent CoreSilent.binaryEval
      simpa [emit, plug_append] using
        Related.eval (w := w) continuation leftLowered sites.append_left nextPlaced
  · simp only [ite_eq_right logical, Option.bind_eq_some_iff] at lowered
    obtain ⟨⟨rf, next⟩, rightLowered, equality⟩ := lowered
    cases equality
    let continuation := KontCode.binaryLeft (left := lf.value)
      (fun eq => logical (Or.inl eq)) (fun eq => logical (Or.inr eq)) rightLowered code
    have facts := code.store_facts placed.storage
    have nextPlaced : Placed p continuation before middle a b :=
      ⟨term_supply leftLowered, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
        ⟨SupplyLE.refl _, Nat.le_refl _, placed.limits⟩, placed.offsets,
        ⟨sites.append_right, placed.sites⟩, placed.currentOffset⟩
    apply Matched.silent CoreSilent.binaryEval
    simpa [emit, plug_append] using
      Related.eval (w := w) continuation leftLowered sites.append_left nextPlaced

theorem eval_read
    (lowered : term offset locals ids (.bufferRead ty resourceIndex index) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b) (sites : ScopedSites offset ids index)
    (found : a.resources[resourceIndex]? = some resource) :
    Matched p q responses ⟨.eval (.bufferRead ty resourceIndex index), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval index, a, .readIndex resource :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨rid, idLookup, ⟨child, middle⟩, childLowered, equality⟩ := lowered
  cases equality
  let continuation := KontCode.readIndex (resource := resource) (index := child.value) (rid := rid) code
  have facts := code.store_facts placed.storage
  have targetLookup := facts.1.resource_lookup idLookup found
  have nextPlaced : Placed p continuation before middle a b :=
    ⟨term_supply childLowered,
      ⟨facts.1, facts.2.1, CapturesHold.cons targetLookup facts.2.2, placed.storage⟩,
      ⟨Nat.le_refl _, placed.limits⟩, placed.offsets, placed.sites, placed.currentOffset⟩
  apply Matched.silent (CoreSilent.readEval found)
  simpa [emit, plug_append] using Related.eval (w := w) continuation childLowered sites nextPlaced

theorem eval_write
    (lowered : term offset locals ids (.bufferWrite ty resourceIndex index value) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b)
    (sites : SiteList offset ids (index.heapSites ++ value.heapSites))
    (found : a.resources[resourceIndex]? = some resource) (permission : resource.mode.CanWrite) :
    Matched p q responses ⟨.eval (.bufferWrite ty resourceIndex index value), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval index, a, .writeIndex resource value :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨rid, idLookup, ⟨child, middle⟩, childLowered, ⟨vf, next⟩, valueLowered, equality⟩ := lowered
  cases equality
  let continuation := KontCode.writeIndex (resource := resource) (index := child.value) (rid := rid) valueLowered code
  have facts := code.store_facts placed.storage
  have targetLookup := facts.1.resource_lookup idLookup found
  have nextPlaced : Placed p continuation before middle a b :=
    ⟨term_supply childLowered,
      ⟨facts.1, facts.2.1, CapturesHold.cons targetLookup facts.2.2, placed.storage⟩,
      ⟨SupplyLE.refl _, Nat.le_refl _, placed.limits⟩, placed.offsets,
      ⟨sites.append_right, placed.sites⟩, placed.currentOffset⟩
  apply Matched.silent (CoreSilent.writeEval found permission)
  simpa [emit, plug_append] using Related.eval (w := w) continuation childLowered sites.append_left nextPlaced

theorem eval_length
    (lowered : term offset locals ids (.bufferLength ty resourceIndex) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b) (found : a.resources[resourceIndex]? = some resource)
    (valid : ANL.Words.legacyResult (APL.checked (resource.length : Int)) ≠ .invalid) :
    Matched p q responses ⟨.eval (.bufferLength ty resourceIndex), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      (ANL.Words.resume (ANL.Words.legacyResult (APL.checked (resource.length : Int))) a k w) := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨rid, idLookup, equality⟩ := lowered
  cases equality
  have facts := code.store_facts placed.storage
  have targetLookup := facts.1.resource_lookup idLookup found
  have dest := placed.destination (middle := before) (SupplyLE.refl _) (Nat.le_refl _)
  apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.lengthFound targetLookup) .zero)) (by decide)
  exact resume_related dest valid

theorem eval_heap
    (lowered : term offset locals ids (.heap ty site length initializer yes no) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b)
    (sites : ScopedSites offset ids (.heap ty site length initializer yes no)) :
    Matched p q responses ⟨.eval (.heap ty site length initializer yes no), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval length, a, .heapLength ⟨a.function, site⟩ initializer yes no :: k, w⟩ := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨⟨lf, middle⟩, lengthLowered, ⟨inf, second⟩, initLowered,
    ⟨yf, third⟩, yesLowered, ⟨nf, next⟩, noLowered, equality⟩ := lowered
  cases equality
  have parts := sites.heap_parts
  let continuation := KontCode.heapLength (site := ⟨a.function, site⟩) (length := lf.value)
    initLowered yesLowered noLowered code
  have facts := code.store_facts placed.storage
  have nextPlaced : Placed p continuation before middle a b :=
    ⟨term_supply lengthLowered, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
      ⟨SupplyLE.refl _, Nat.le_refl _, placed.limits⟩, placed.offsets,
      ⟨parts.1, parts.2.2.1, parts.2.2.2.1, parts.2.2.2.2, placed.sites⟩, placed.currentOffset⟩
  apply Matched.silent CoreSilent.heapEval
  simpa [emit, plug_append] using Related.eval (w := w) continuation lengthLowered parts.2.1 nextPlaced

theorem eval_call
    (lowered : term offset locals ids (.call ty functionId args) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b)
    (sites : SiteList offset ids (args.flatMap Term.heapSites)) :
    Matched p q responses ⟨.eval (.call ty functionId args), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      (beginArguments functionId none args [] a k w) := by
  cases args with
  | nil =>
      simp only [term, arguments, bind, Option.bind_some, Option.pure_def, Option.some.injEq] at lowered
      cases lowered
      have dest := placed.destination (middle := before) (SupplyLE.refl _) (Nat.le_refl _)
      apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.callFound (by rfl)) .zero)) (by decide)
      exact Related.invoke (KontCode.destination code) dest
  | cons first rest =>
      simp only [term, arguments, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨argf, ⟨⟨ff, middle⟩, firstLowered, ⟨rf, next⟩, restLowered, eqArgs⟩, equality⟩ := lowered
      cases eqArgs
      cases equality
      let continuation := KontCode.arguments (f := functionId) (prior := [])
        (current := ff.value) (done := []) restLowered code
      have facts := code.store_facts placed.storage
      have nextPlaced : Placed p continuation before middle a b :=
        ⟨term_supply firstLowered,
          ⟨facts.1, facts.2.1, CapturesHold.cons (by rfl) facts.2.2, placed.storage⟩,
          ⟨SupplyLE.refl _, Nat.le_refl _, placed.limits⟩, placed.offsets,
          ⟨fun e he => sites.flatMap_tail.flatMap_member he, placed.sites⟩, placed.currentOffset⟩
      apply Matched.silent CoreSilent.call
      simpa [emit, plug_append, beginArguments] using
        Related.eval (w := w) continuation firstLowered (sites.flatMap_member (.head _)) nextPlaced

theorem eval_tuple
    (lowered : term offset locals ids (.tuple ty (first :: rest)) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b)
    (sites : SiteList offset ids ((first :: rest).flatMap Term.heapSites)) :
    Matched p q responses ⟨.eval (.tuple ty (first :: rest)), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      ⟨.eval first, a, .fields rest [] :: k, w⟩ := by
  simp only [term, arguments, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨argf, ⟨⟨ff, middle⟩, firstLowered, ⟨rf, next⟩, restLowered, eqArgs⟩, equality⟩ := lowered
  cases eqArgs
  cases equality
  let continuation := KontCode.fields (prior := []) (current := ff.value) (done := []) restLowered code
  have facts := code.store_facts placed.storage
  have nextPlaced : Placed p continuation before middle a b :=
    ⟨term_supply firstLowered,
      ⟨facts.1, facts.2.1, CapturesHold.cons (by rfl) facts.2.2, placed.storage⟩,
      ⟨SupplyLE.refl _, Nat.le_refl _, placed.limits⟩, placed.offsets,
      ⟨fun e he => sites.flatMap_tail.flatMap_member he, placed.sites⟩, placed.currentOffset⟩
  apply Matched.silent CoreSilent.tupleFirst
  simpa [emit, plug_append] using
    Related.eval (w := w) continuation firstLowered (sites.flatMap_member (.head _)) nextPlaced

theorem eval_view
    (lowered : term offset locals ids (.callView ty functionId resourceIndex mode args) before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b) (sites : SiteList offset ids (args.flatMap Term.heapSites))
    (found : a.resources[resourceIndex]? = some resource) (permission : resource.mode.CanLend mode) :
    Matched p q responses ⟨.eval (.callView ty functionId resourceIndex mode args), a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
      (beginArguments functionId (some ⟨resource, mode⟩) args [] a k w) := by
  simp only [term, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨rid, idLookup, argf, argsLowered, equality⟩ := lowered
  cases equality
  have facts := code.store_facts placed.storage
  have targetLookup := facts.1.resource_lookup idLookup found
  cases args with
  | nil =>
      simp only [arguments, Option.some.injEq] at argsLowered
      cases argsLowered
      have dest := placed.destination (middle := before) (SupplyLE.refl _) (Nat.le_refl _)
      apply Matched.positive (.succ Mir.Step.instruction
        (.succ (Mir.Step.viewFound targetLookup (by rfl) permission) .zero)) (by decide)
      exact Related.invoke (KontCode.destination code) dest
  | cons first rest =>
      simp only [arguments, bind, Option.bind_eq_some_iff, Option.pure_def] at argsLowered
      obtain ⟨⟨ff, middle⟩, firstLowered, ⟨rf, next⟩, restLowered, equality⟩ := argsLowered
      cases equality
      let continuation := KontCode.viewArguments (f := functionId) (sourceLoan := ⟨resource, mode⟩)
        (prior := []) (current := ff.value) (rid := rid) (done := []) restLowered code
      have nextPlaced : Placed p continuation before middle a b :=
        ⟨term_supply firstLowered,
          ⟨facts.1, facts.2.1, CapturesHold.cons targetLookup (CapturesHold.cons (by rfl) facts.2.2), placed.storage⟩,
          ⟨SupplyLE.refl _, Nat.le_refl _, placed.limits⟩, placed.offsets,
          ⟨fun e he => sites.flatMap_tail.flatMap_member he, placed.sites⟩, placed.currentOffset⟩
      apply Matched.silent (CoreSilent.callView found permission)
      simpa [emit, plug_append, beginArguments] using
        Related.eval (w := w) continuation firstLowered (sites.flatMap_member (.head _)) nextPlaced

/-- Every actual step out of a checked source expression matches its canonical fragment. -/
theorem eval_step (wf : WellFormedProgram p)
    (typed : State.Typed p ⟨.eval e, a, k, w⟩ ty)
    (step : Step p responses ⟨.eval e, a, k, w⟩ next)
    (lowered : term offset locals ids e before = some (fragment, after))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p code before after a b) (sites : ScopedSites offset ids e) :
    Matched p q responses ⟨.eval e, a, k, w⟩
      ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩ next := by
  have nextTyped := preservation wf typed step
  cases step with
  | lit => exact eval_lit lowered code placed
  | word => exact eval_word lowered code placed (resume_valid_of_typed nextTyped)
  | localFound found => exact eval_local lowered code placed found
  | localMissing => exact False.elim (nextTyped.not_invalid rfl)
  | letEval => exact eval_let lowered code placed (by simpa only [ScopedSites, Term.heapSites, SiteList] using sites)
  | letMutEval => exact eval_letMut lowered code placed (by simpa only [ScopedSites, Term.heapSites, SiteList] using sites)
  | assignEval => exact eval_assign lowered code placed (by simpa only [ScopedSites, Term.heapSites] using sites)
  | whileEval => exact eval_while lowered code placed (by simpa only [ScopedSites, Term.heapSites, SiteList] using sites)
  | ifEval => exact eval_if lowered code placed (by simpa only [ScopedSites, Term.heapSites, SiteList] using sites)
  | convertEval => exact eval_convert lowered code placed (by simpa only [ScopedSites, Term.heapSites] using sites)
  | unaryEval => exact eval_unary lowered code placed (by simpa only [ScopedSites, Term.heapSites] using sites)
  | binaryEval => exact eval_binary lowered code placed (by simpa only [ScopedSites, Term.heapSites, SiteList] using sites)
  | call => exact eval_call lowered code placed (by simpa only [ScopedSites, Term.heapSites, SiteList] using sites)
  | tupleEmpty => exact False.elim (nextTyped.not_invalid rfl)
  | tupleFirst => exact eval_tuple lowered code placed (by simpa only [ScopedSites, Term.heapSites, SiteList] using sites)
  | projectEval => exact eval_project lowered code placed (by simpa only [ScopedSites, Term.heapSites] using sites)
  | heapEval => exact eval_heap lowered code placed sites
  | lengthFound found => exact eval_length lowered code placed found (resume_valid_of_typed nextTyped)
  | lengthMissing => exact False.elim (nextTyped.not_invalid rfl)
  | readEval found => exact eval_read lowered code placed (by simpa only [ScopedSites, Term.heapSites] using sites) found
  | readMissing => exact False.elim (nextTyped.not_invalid rfl)
  | writeEval found permission =>
      exact eval_write lowered code placed (by simpa only [ScopedSites, Term.heapSites, SiteList] using sites) found permission
  | writeMissing => exact False.elim (nextTyped.not_invalid rfl)
  | writeDenied => exact False.elim (nextTyped.not_invalid rfl)
  | callView found permission =>
      exact eval_view lowered code placed (by simpa only [ScopedSites, Term.heapSites, SiteList] using sites) found permission
  | viewMissing => exact False.elim (nextTyped.not_invalid rfl)
  | viewDenied => exact False.elim (nextTyped.not_invalid rfl)

end ANL.Words.Simulation
