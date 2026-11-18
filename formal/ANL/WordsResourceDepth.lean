import ANL.WordsResourceAccounting

namespace ANL.Words.Tool

open ANL.Memory

set_option linter.unusedSimpArgs false

/-- An expression whose first transition enters a child and retains its parent frame. -/
inductive ChildTerm : Term → Prop where
  | letE : ChildTerm (.letE t e b)
  | letMut : ChildTerm (.letMut t e b)
  | assign : ChildTerm (.assign t i e)
  | whileE : ChildTerm (.whileE t c b)
  | ifE : ChildTerm (.ifE t c y n)
  | convert : ChildTerm (.convert t mode target e)
  | unary : ChildTerm (.unary t op e)
  | binary : ChildTerm (.binary t op e b)
  | tuple : ChildTerm (.tuple t (e :: rest))
  | project : ChildTerm (.project t e i)
  | heap : ChildTerm (.heap t h len init yes no)
  | read : ChildTerm (.bufferRead t i index)
  | write : ChildTerm (.bufferWrite t i index value)
  | call : ChildTerm (.call t f (e :: rest))
  | callView : ChildTerm (.callView t f i mode (e :: rest))

inductive LeafTerm : Term → Prop where
  | word : LeafTerm (.word t width value)
  | lit : LeafTerm (.lit t value)
  | local : LeafTerm (.local t i)
  | length : LeafTerm (.bufferLength t i)

/-- Returning through these frames completes their expression, with no further child. -/
inductive PopFrame : Frame → Prop where
  | scope : PopFrame .scope
  | assign : PopFrame (.assign i)
  | convert : PopFrame (.convert mode target)
  | unary : PopFrame (.unary op)
  | right : PopFrame (.right op left)
  | fields : PopFrame (.fields [] prior)
  | project : PopFrame (.project i)
  | heapLength : PopFrame (.heapLength site init yes no)
  | heapInitial : PopFrame (.heapInitial site n yes no)
  | readIndex : PopFrame (.readIndex binding)
  | writeIndex : PopFrame (.writeIndex binding value)
  | writeValue : PopFrame (.writeValue binding i)

inductive SiblingFrame : Frame → Prop where
  | bind : SiblingFrame (.bind permission body)
  | arguments : SiblingFrame (.arguments f loan (e :: rest) values)
  | fields : SiblingFrame (.fields (e :: rest) values)
  | body : SiblingFrame (.body condition body)

inductive PassiveControl : Control → Prop where
  | readCheck : PassiveControl (.readCheck binding index)
  | readCell : PassiveControl (.readCell binding index)
  | store : PassiveControl (.store binding index value)
  | invoke : PassiveControl (.invoke f loan values)
  | revoke : PassiveControl (.revoke value)

/-- Independent recursive-nesting rules; no resource runner or metadata-update function appears here. -/
inductive Nesting : State → Nat → List Nat → State → Nat → List Nat → Prop where
  | child : ChildTerm term →
      Nesting ⟨.eval term, a, k, w⟩ d ds next (d + 1) (d :: ds)
  | leaf : LeafTerm term → Nesting ⟨.eval term, a, k, w⟩ d ds next d ds
  | callEmpty : Nesting ⟨.eval (.call t f []), a, k, w⟩ d ds next (d + 1) ds
  | viewEmpty : Nesting ⟨.eval (.callView t f i mode []), a, k, w⟩ d ds next (d + 1) ds
  | popFrame : PopFrame frame → ds ≠ [] →
      Nesting ⟨.ret value, a, frame :: k, w⟩ d ds next (ds.headD d) ds.tail
  | sibling : SiblingFrame frame → ds ≠ [] →
      Nesting ⟨.ret value, a, frame :: k, w⟩ d ds next (ds.headD d + 1) ds
  | ifBranch : ds ≠ [] →
      Nesting ⟨.ret value, a, .ifF yes no :: k, w⟩ d ds next (ds.headD d + 1) ds.tail
  | argumentsDone : ds ≠ [] →
      Nesting ⟨.ret value, a, .arguments f loan [] values :: k, w⟩ d ds next (ds.headD d + 1) ds.tail
  | rightChild : ds ≠ [] →
      Nesting ⟨.ret value, a, .left op right :: k, w⟩ d ds ⟨.eval right, a2, k2, w2⟩ (ds.headD d + 1) ds
  | shortCircuit : ds ≠ [] →
      Nesting ⟨.ret value, a, .left op right :: k, w⟩ d ds ⟨.ret result, a2, k2, w2⟩ (ds.headD d) ds.tail
  | loopBody : ds ≠ [] →
      Nesting ⟨.ret value, a, .condition condition body :: k, w⟩ d ds ⟨.eval body, a2, k2, w2⟩ (ds.headD d + 1) ds
  | loopDone : ds ≠ [] →
      Nesting ⟨.ret value, a, .condition condition body :: k, w⟩ d ds ⟨.ret result, a2, k2, w2⟩ (ds.headD d) ds.tail
  | callResult : Nesting ⟨.ret value, a, .callReturn caller loan :: k, w⟩ d ds next d ds
  | ownerResult : Nesting ⟨.ret value, a, .owner binding site :: k, w⟩ d ds next d ds
  | initialChild : Nesting ⟨.lengthReady site value init yes no, a, k, w⟩ d ds
      ⟨.eval init, a2, k2, w2⟩ (d + 1) (d :: ds)
  | negative : Nesting ⟨.lengthReady site value init yes no, a, k, w⟩ d ds
      ⟨.trap kind, a2, k2, w2⟩ d ds
  | writeChild : Nesting ⟨.writeCheck binding index value, a, k, w⟩ d ds
      ⟨.eval value, a2, k2, w2⟩ (d + 1) (d :: ds)
  | writeBounds : Nesting ⟨.writeCheck binding index value, a, k, w⟩ d ds
      ⟨.trap kind, a2, k2, w2⟩ d ds
  | passive : PassiveControl ctrl → Nesting ⟨ctrl, a, k, w⟩ d ds next d ds
  | grant : Nesting ⟨.grant f loan values, a, k, w⟩ d ds next d (d :: ds)
  | close : ds ≠ [] → Nesting ⟨.close binding site value, a, k, w⟩ d ds next (ds.headD d) ds.tail
  | restore : ds ≠ [] → Nesting ⟨.restore value, a, k, w⟩ d ds next (ds.headD d) ds.tail
  | allocated : Nesting ⟨.allocate site n init yes no, a, k, w⟩ d ds
      ⟨.eval yes, a2, .owner binding site :: k, w2⟩ (d + 1) (d :: ds)
  | failure : Nesting ⟨.allocate site n init yes no, a, k, w⟩ d ds
      ⟨.eval no, a2, k, w2⟩ (d + 1) ds

inductive DepthReachable (p : Program) (responses : Responses) : State → Nat → List Nat → Prop where
  | initial : DepthReachable p responses (ANL.Words.initial p) 0 []
  | next : DepthReachable p responses s d ds → Step p responses s next →
      Nesting s d ds next d2 ds2 → DepthReachable p responses next d2 ds2

 theorem aligned_nonempty (h : Aligned ⟨ctrl, a, frame :: k, w⟩ m) : m.parents ≠ [] := by
  intro empty
  simp [Aligned, empty] at h

 theorem finish_nesting (hs : Step p responses s next) (na : NotAllocation s.control)
    (safe : next.control ≠ .invalid) (aligned : Aligned s m) :
    Nesting s m.depth m.parents next (finish s next m).depth (finish s next m).parents := by
  cases hs <;> simp only [NotAllocation] at na
  all_goals try contradiction
  all_goals try { exact False.elim (safe rfl) }
  all_goals try { exact .child (by constructor) }
  all_goals try { exact .leaf (by constructor) }
  all_goals try { exact .popFrame (by constructor) (aligned_nonempty aligned) }
  all_goals try { exact .sibling (by constructor) (aligned_nonempty aligned) }
  all_goals try { exact .passive (by constructor) }
  all_goals try { exact .ifBranch (aligned_nonempty aligned) }
  all_goals try { exact .rightChild (aligned_nonempty aligned) }
  all_goals try { exact .shortCircuit (aligned_nonempty aligned) }
  all_goals try { exact .loopBody (aligned_nonempty aligned) }
  all_goals try { exact .loopDone (aligned_nonempty aligned) }
  all_goals try { exact .callResult }
  all_goals try { exact .ownerResult }
  all_goals try { exact .initialChild }
  all_goals try { exact .negative }
  all_goals try { exact .writeChild }
  all_goals try { exact .writeBounds }
  all_goals try { exact .grant }
  all_goals try { exact .close (aligned_nonempty aligned) }
  all_goals try { exact .restore (aligned_nonempty aligned) }

  case call t f args a k w =>
    cases args with
    | nil => exact .callEmpty
    | cons e rest => exact .child .call
  case callView i binding t f mode args a k w found permission =>
    cases args with
    | nil => exact .viewEmpty
    | cons e rest => exact .child .callView
  case argumentReturn value a f loan rest values k w =>
    cases rest with
    | nil => exact .argumentsDone (aligned_nonempty aligned)
    | cons e rest => exact .sibling .arguments (aligned_nonempty aligned)
  case lengthFound i binding t a k w found =>
    cases hr : legacyResult (APL.checked (binding.length : Int)) <;> simp only [hr, resume] at safe ⊢
    all_goals try { exact False.elim (safe rfl) }
    all_goals exact .leaf .length
  case word t width value a k w =>
    cases hr : wordLiteral width value <;> simp only [hr, resume] at safe ⊢
    all_goals try { exact False.elim (safe rfl) }
    all_goals exact .leaf .word
  case convertReturn v a mode target k w =>
    cases hr : convert mode target v <;> simp only [hr, resume] at safe ⊢
    all_goals try { exact False.elim (safe rfl) }
    all_goals exact .popFrame .convert (aligned_nonempty aligned)
  case unaryReturn v a op k w =>
    cases hr : unary op v <;> simp only [hr, resume] at safe ⊢
    all_goals try { exact False.elim (safe rfl) }
    all_goals exact .popFrame .unary (aligned_nonempty aligned)
  case binaryReturn v a op left k w =>
    cases hr : binary op left v <;> simp only [hr, resume] at safe ⊢
    all_goals try { exact False.elim (safe rfl) }
    all_goals exact .popFrame .right (aligned_nonempty aligned)
  case fieldsDone v a values k w =>
    cases hr : construct (v :: values).reverse <;> simp only [hr, resume] at safe ⊢
    all_goals try { exact False.elim (safe rfl) }
    all_goals exact .popFrame .fields (aligned_nonempty aligned)
  case projectReturn v a i k w =>
    cases hr : project v i <;> simp only [hr, resume] at safe ⊢
    all_goals try { exact False.elim (safe rfl) }
    all_goals exact .popFrame .project (aligned_nonempty aligned)

 theorem commit_nesting (wf : WellFormedProgram p) (typed : State.Typed p s ty)
    (aligned : Aligned s m) (hp : preflight p s m = .allowed charged)
    (hc : commit p responses s charged = some last) :
    Nesting s m.depth m.parents last.machine last.meter.depth last.meter.parents := by
  have depthEq := preflight_depth hp
  have parentsEq := preflight_parents hp
  have aligned2 : Aligned s charged := by simpa [Aligned, parentsEq] using aligned
  by_cases na : NotAllocation s.control
  · rw [commit_nonallocation na] at hc
    cases hs : step p responses s with
    | none => simp [hs] at hc
    | some next =>
      simp only [hs, Option.map_some, Option.some.injEq] at hc
      subst last
      have path := step_sound hs
      have hn := finish_nesting path na (preservation wf typed path).not_invalid aligned2
      simpa only [depthEq, parentsEq] using hn
  · rcases s with ⟨control, a, k, w⟩
    cases control <;> simp only [NotAllocation] at na
    all_goals try contradiction
    case allocate site n init yes no =>
      cases ha : allocate p.profile responses w site n init with
      | mk result after =>
        cases result <;> simp only [commit, ha, Option.some.injEq] at hc <;> subst last
        · simpa only [Meter.pushChild, depthEq, parentsEq] using
            (Nesting.allocated (a := a) (a2 := {a with resources := ⟨.owner, _, n⟩ :: a.resources})
              (d := m.depth) (ds := m.parents) (site := site) (n := n) (init := init)
              (yes := yes) (no := no) (k := k) (w := w) (w2 := after) (binding := ⟨.owner, _, n⟩))
        · simpa only [Meter.release, depthEq, parentsEq] using
            (Nesting.failure (a := a) (a2 := a) (d := m.depth) (ds := m.parents) (site := site)
              (n := n) (init := init) (yes := yes) (no := no) (k := k) (w := w) (w2 := after))
        · simpa only [depthEq, parentsEq] using
            (Nesting.failure (a := a) (a2 := a) (d := m.depth) (ds := m.parents) (site := site)
              (n := n) (init := init) (yes := yes) (no := no) (k := k) (w := w) (w2 := after))

 theorem blocked_depth (hp : preflight p s m = .blocked reason retained) :
    retained.depth = m.depth ∧ retained.parents = m.parents := by
  have same := preflight_blocked_reservations hp
  simp only [Meter.reservations, Prod.mk.injEq] at same
  exact same.2.2.2

 theorem tick_depth (wf : WellFormedProgram p) (typed : State.Typed p c.machine ty)
    (account : Accounted c.machine c.meter)
    (origin : DepthReachable p responses c.machine c.meter.depth c.meter.parents) :
    DepthReachable p responses (tick p responses c).configuration.machine
      (tick p responses c).configuration.meter.depth (tick p responses c).configuration.meter.parents := by
  unfold tick
  split
  · exact origin
  next nonstopped =>
    split
    next hp =>
      obtain ⟨depthEq, parentsEq⟩ := blocked_depth hp
      simpa only [Tick.configuration, depthEq, parentsEq] using origin
    next hp =>
      split
      next hc => exact False.elim (nonstopped (commit_none hc))
      next hc => exact .next origin (commit_sound hc) (commit_nesting wf typed account.1 hp hc)

 theorem run_depth (wf : WellFormedProgram p) (typed : State.Typed p c.machine ty)
    (account : Accounted c.machine c.meter)
    (origin : DepthReachable p responses c.machine c.meter.depth c.meter.parents) :
    DepthReachable p responses (run p responses budget c).configuration.machine
      (run p responses budget c).configuration.meter.depth (run p responses budget c).configuration.meter.parents := by
  induction budget generalizing c with
  | zero => unfold run; split <;> exact origin
  | succ budget ih =>
    have hd := tick_depth wf typed account origin
    have ha := tick_accounted (responses := responses) wf typed account
    unfold run
    cases ht : tick p responses c with
    | completed last => simpa [ht, Tick.configuration, Result.configuration] using hd
    | resourceLimit reason last => simpa [ht, Tick.configuration, Result.configuration] using hd
    | advanced next =>
      have depth : DepthReachable p responses next.machine next.meter.depth next.meter.parents := by
        simpa [ht, Tick.configuration] using hd
      have counted : Accounted next.machine next.meter := by simpa [ht, Tick.configuration] using ha
      exact ih (preservation wf typed (tick_advanced ht)) counted depth

 theorem run_entry_depth (wf : WellFormedProgram p) :
    DepthReachable p responses (run p responses budget (initial p fuel)).configuration.machine
      (run p responses budget (initial p fuel)).configuration.meter.depth
      (run p responses budget (initial p fuel)).configuration.meter.parents :=
  run_depth wf (entry_typed wf) initial_accounted .initial

 theorem depth_limit (bound : maxDepth ≤ m.depth) :
    tick p responses ⟨⟨.eval term, a, k, w⟩, m⟩ =
      .resourceLimit .depth ⟨⟨.eval term, a, k, w⟩, m⟩ := by
  simp [tick, isStopped, preflight, depth_before_fuel bound]

end ANL.Words.Tool
