import ANL.MemoryResourceRun
import ANL.MemoryResourcePolicy

namespace ANL.Memory.Tool

set_option linter.unusedSimpArgs false

 def NotAllocation : Control → Prop
  | .allocate _ _ _ _ _ => False
  | _ => True

 theorem finish_aligned (hs : Step p responses s next) (na : NotAllocation s.control)
    (safe : next.control ≠ .invalid) (aligned : Aligned s m) : Aligned next (finish s next m) := by
  cases hs <;> simp only [NotAllocation] at na
  all_goals try contradiction
  all_goals try { exact False.elim (safe rfl) }
  all_goals try { simp_all [Aligned, finish, Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent,
    Meter.sibling, Meter.tailChild, Meter.release, List.length_tail] }
  case call t f args a k w =>
    cases args <;> simp_all [beginArguments, Aligned, finish, Meter.pushChild]
  case callView i binding t f mode args a k w found permission =>
    cases args <;> simp_all [beginArguments, Aligned, finish, Meter.pushChild]
  case argumentReturn v a f loan rest values k w =>
    cases rest <;> simp_all [beginArguments, Aligned, finish, Meter.tailChild, Meter.sibling, List.length_tail]
  case lengthFound i binding t a k w found =>
    cases hr : APL.FlatProducts.embedResult (APL.checked (binding.length : Int)) <;>
      simp_all [resume, Aligned, finish]
  case unaryReturn v a op k w =>
    cases hr : APL.FlatProducts.unary op v <;>
      simp_all [resume, Aligned, finish, Meter.pop, List.length_tail]
  case binaryReturn v a op left k w =>
    cases hr : APL.FlatProducts.binary op left v <;>
      simp_all [resume, Aligned, finish, Meter.pop, List.length_tail]
  case fieldsDone v a values k w =>
    cases hr : APL.FlatProducts.construct (v :: values).reverse <;>
      simp_all [resume, Aligned, finish, Meter.pop, List.length_tail]
  case projectReturn v a i k w =>
    cases hr : APL.FlatProducts.project v i <;>
      simp_all [resume, Aligned, finish, Meter.pop, List.length_tail]

 theorem env_update_length (h : APL.FlatProducts.update env i v = some next) : next.length = env.length := by
  induction env generalizing i next with
  | nil => simp [APL.FlatProducts.update] at h
  | cons first rest ih =>
    cases i with
    | zero => simp [APL.FlatProducts.update] at h; subst next; rfl
    | succ i =>
      cases hu : APL.FlatProducts.update rest i v with
      | none => simp [APL.FlatProducts.update, hu] at h
      | some tail =>
        simp [APL.FlatProducts.update, hu] at h
        subst next
        simp [ih hu]

 theorem finish_slots (typed : State.Typed p s ty) (hs : Step p responses s next) (na : NotAllocation s.control)
    (safe : next.control ≠ .invalid) (counted : m.slots = logicalSlots s) :
    (finish s next (paid p s m)).slots = logicalSlots next := by
  cases hs <;> simp only [NotAllocation] at na
  all_goals try contradiction
  all_goals try { exact False.elim (safe rfl) }
  all_goals try { simp_all [finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
    Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
    logicalSlots, savedSlots, pendingSlots, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] }

  case call t f args a k w =>
    cases args <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  case callView i binding t f mode args a k w found permission =>
    cases args <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  case argumentReturn v a f loan rest values k w =>
    cases rest <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  case scopeReturn cell rest v a k w envEq =>
    simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    omega
  case assignReturn i v env a k w updated =>
    have same := env_update_length updated
    simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  case closed after binding site value a k w closed =>
    obtain ⟨tail, rest, _, hr, _, _⟩ := typed.layout.owner_inv
    simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    omega
  case restore value a caller loan k w =>
    simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    omega
  case lengthFound i binding t a k w found =>
    cases hr : APL.FlatProducts.embedResult (APL.checked (binding.length : Int)) <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  case unaryReturn v a op k w =>
    cases hr : APL.FlatProducts.unary op v <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  case binaryReturn v a op left k w =>
    cases hr : APL.FlatProducts.binary op left v <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  case fieldsDone v a values k w =>
    cases hr : APL.FlatProducts.construct (v :: values).reverse <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  case projectReturn v a i k w =>
    cases hr : APL.FlatProducts.project v i <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
      logicalSlots, savedSlots, pendingSlots, loanResources, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

 theorem finish_cells (typed : State.Typed p s ty) (hs : Step p responses s next)
    (na : NotAllocation s.control) (safe : next.control ≠ .invalid) (counted : m.liveCells = s.world.liveCells) :
    (finish s next (paid p s m)).liveCells = next.world.liveCells := by
  cases hs <;> simp only [NotAllocation] at na
  all_goals try contradiction
  all_goals try { exact False.elim (safe rfl) }
  all_goals try { simp_all [finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
    Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release] }

  case call t f args a k w =>
    cases args <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release]
  case callView i binding t f mode args a k w found permission =>
    cases args <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release]
  case argumentReturn v a f loan rest values k w =>
    cases rest <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release]
  case lengthFound i binding t a k w found =>
    cases hr : APL.FlatProducts.embedResult (APL.checked (binding.length : Int)) <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release]
  case unaryReturn v a op k w =>
    cases hr : APL.FlatProducts.unary op v <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release]
  case binaryReturn v a op left k w =>
    cases hr : APL.FlatProducts.binary op left v <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release]
  case fieldsDone v a values k w =>
    cases hr : APL.FlatProducts.construct (v :: values).reverse <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release]
  case projectReturn v a i k w =>
    cases hr : APL.FlatProducts.project v i <;> simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release]
  case stored after binding i value a k w written =>
    have same := World.write_liveCells written
    simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release]
  case closed after binding site value a k w closed =>
    obtain ⟨tail, rest, _, hr, _, _⟩ := typed.layout.owner_inv
    have member : binding ∈ a.resources := by
      change a.resources = binding :: rest at hr
      rw [hr]
      exact List.mem_cons_self
    obtain ⟨owner, found, lengthEq⟩ := typed.lookup member
    obtain ⟨owner2, found2, sum⟩ := World.close_liveCells closed
    have same : owner2 = owner := Option.some.inj (found2.symm.trans found)
    subst owner2
    simp_all [beginArguments, resume, finish, paid, slotCharge, cellCharge, tupleCharge, entryCharge,
      Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release]
    omega

 theorem allocation_rejected_iff :
    (allocate profile responses w site n init).1 = .targetRejected ↔ profile.maxCells < n := by
  unfold allocate
  split
  · simp_all
  · split
    · simp_all
    · cases responses w.nextRequest <;> simp_all

 theorem allocation_success_cells
    (h : allocate profile responses w site n init = (.allocated ref, after)) :
    after.liveCells = n + w.liveCells := by
  have shapes := allocate_shapes h
  have sums := congrArg (fun xs => (xs.map Shape.length).sum) shapes
  simpa [World.liveCells, List.map_map, Function.comp_def, Owner.shape] using sums

 theorem commit_nonallocation (h : NotAllocation s.control) : commit p responses s m =
    (step p responses s).map (fun next => ⟨next, finish s next m⟩) := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp only [commit]
  all_goals try { cases step p responses _ <;> rfl }
  exact False.elim h

 theorem finish_accounted (typed : State.Typed p s ty) (hs : Step p responses s next)
    (na : NotAllocation s.control) (safe : next.control ≠ .invalid) (account : Accounted s m)
    (hp : preflight p s m = .allowed charged) : Accounted next (finish s next charged) := by
  have bound : charged.Bounded := by
    have h := preflight_bounded (p := p) (s := s) account.2.2.2
    simpa [hp, Preflight.meter] using h
  have align : Aligned s charged := by simpa [Aligned, preflight_parents hp] using account.1
  refine ⟨finish_aligned hs na safe align, ?_, ?_, finish_bounded bound⟩
  · rw [preflight_paid hp]; exact finish_slots typed hs na safe account.2.1
  · rw [preflight_paid hp]; exact finish_cells typed hs na safe account.2.2.1

 theorem commit_accounted (wf : WellFormedProgram p) (typed : State.Typed p s ty)
    (account : Accounted s m) (hp : preflight p s m = .allowed charged)
    (hc : commit p responses s charged = some last) : Accounted last.machine last.meter := by
  by_cases na : NotAllocation s.control
  · rw [commit_nonallocation na] at hc
    cases hs : step p responses s with
    | none => simp [hs] at hc
    | some next =>
      simp only [hs, Option.map_some, Option.some.injEq] at hc
      subst last
      have path := step_sound hs
      exact finish_accounted typed path na (preservation wf typed path).not_invalid account hp
  · rcases s with ⟨control, a, k, w⟩
    cases control <;> simp only [NotAllocation] at na
    all_goals try contradiction
    case allocate site n init yes no =>
      have bound : charged.Bounded := by
        have h := preflight_bounded (p := p) (s := ⟨.allocate site n init yes no, a, k, w⟩) account.2.2.2
        simpa [hp, Preflight.meter] using h
      cases ha : allocate p.profile responses w site n init with
      | mk result after =>
        cases result with
        | allocated ref =>
          have eligible : n ≤ p.profile.maxCells := by
            by_cases good : n ≤ p.profile.maxCells
            · exact good
            · rw [allocate_target (by omega : p.profile.maxCells < n)] at ha
              cases ha
          have cells := allocation_success_cells ha
          simp only [commit, ha, Option.some.injEq] at hc
          subst last
          rw [preflight_paid hp]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [Aligned, Meter.pushChild, paid] using account.1
          · simp [Meter.pushChild, paid, slotCharge, eligible, logicalSlots, savedSlots, pendingSlots,
              account.2.1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          · simp [Meter.pushChild, paid, cellCharge, eligible, account.2.2.1, cells, Nat.add_comm]
          · simpa [preflight_paid hp, Meter.pushChild, Meter.Bounded] using bound
        | refused =>
          have eligible : n ≤ p.profile.maxCells := by
            by_cases good : n ≤ p.profile.maxCells
            · exact good
            · rw [allocate_target (by omega : p.profile.maxCells < n)] at ha
              cases ha
          have owners := allocate_failure_owners ha (Or.inl rfl)
          simp only [commit, ha, Option.some.injEq] at hc
          subst last
          rw [preflight_paid hp]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [Aligned, paid, Meter.release] using account.1
          · simp [paid, Meter.release, slotCharge, eligible, logicalSlots, pendingSlots, account.2.1]
          · simp [paid, Meter.release, cellCharge, eligible, World.liveCells, owners, account.2.2.1]
          · simpa [preflight_paid hp, Meter.Bounded, Meter.release] using (release_bounded (slots := 1) (cells := n) bound)
        | targetRejected =>
          have rejected : p.profile.maxCells < n := allocation_rejected_iff.mp (by rw [ha])
          have noCharge : charged = m := by simpa [rejected_allocation rejected] using hp.symm
          subst charged
          have owners := allocate_failure_owners ha (Or.inr rfl)
          simp only [commit, ha, Option.some.injEq] at hc
          subst last
          refine ⟨account.1, ?_, ?_, bound⟩
          · simpa [logicalSlots, pendingSlots] using account.2.1
          · simpa [World.liveCells, owners] using account.2.2.1

 theorem blocked_accounted (account : Accounted s m)
    (hp : preflight p s m = .blocked reason retained) : Accounted s retained := by
  have same := preflight_blocked_reservations hp
  rcases m with ⟨fuel, slots, cells, fields, depth, parents⟩
  rcases retained with ⟨fuel2, slots2, cells2, fields2, depth2, parents2⟩
  simp only [Meter.reservations, Prod.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact account

 def Tick.configuration : Tick → Configuration
  | .completed c | .resourceLimit _ c | .advanced c => c

 theorem tick_accounted (wf : WellFormedProgram p) (typed : State.Typed p c.machine ty)
    (account : Accounted c.machine c.meter) :
    Accounted (tick p responses c).configuration.machine (tick p responses c).configuration.meter := by
  unfold tick
  split
  · exact account
  next nonstopped =>
    split
    next hp => exact blocked_accounted account hp
    next hp =>
      split
      next hc => exact False.elim (nonstopped (commit_none hc))
      next hc => exact commit_accounted wf typed account hp hc

 theorem run_accounted (wf : WellFormedProgram p) (typed : State.Typed p c.machine ty)
    (account : Accounted c.machine c.meter) :
    Accounted (run p responses budget c).configuration.machine (run p responses budget c).configuration.meter := by
  induction budget generalizing c with
  | zero => unfold run; split <;> exact account
  | succ budget ih =>
    have nextAccount := tick_accounted (responses := responses) wf typed account
    unfold run
    cases ht : tick p responses c with
    | completed last => simpa [ht, Tick.configuration, Result.configuration] using nextAccount
    | resourceLimit reason last => simpa [ht, Tick.configuration, Result.configuration] using nextAccount
    | advanced next =>
      have account2 : Accounted next.machine next.meter := by simpa [ht, Tick.configuration] using nextAccount
      exact ih (preservation wf typed (tick_advanced ht)) account2

 theorem initial_accounted : Accounted (initial p fuel).machine (initial p fuel).meter := by
  simp [initial, ANL.Memory.initial, Meter.empty, Accounted, Aligned, logicalSlots, savedSlots, pendingSlots,
    loanResources, World.liveCells, World.initial, Meter.Bounded, maxSlots, maxLiveCells, maxTupleFields]

 theorem run_entry_accounted (wf : WellFormedProgram p) :
    Accounted (run p responses budget (initial p fuel)).configuration.machine
      (run p responses budget (initial p fuel)).configuration.meter :=
  run_accounted wf (entry_typed wf) initial_accounted

 theorem run_entry_limits (wf : WellFormedProgram p) :
    let last := (run p responses budget (initial p fuel)).configuration
    last.machine.world.liveCells ≤ maxLiveCells ∧ logicalSlots last.machine ≤ maxSlots ∧
      last.meter.tupleFields ≤ maxTupleFields := by
  have h := run_entry_accounted (responses := responses) (budget := budget) (fuel := fuel) wf
  exact ⟨h.2.2.1 ▸ h.2.2.2.2.1, h.2.1 ▸ h.2.2.2.1, h.2.2.2.2.2⟩

 theorem tick_blocked (stop : isStopped c.machine = false)
    (hp : preflight p c.machine c.meter = .blocked reason retained) :
    tick p responses c = .resourceLimit reason ⟨c.machine, retained⟩ := by simp [tick, stop, hp]

 theorem blocked_response_independent (stop : isStopped c.machine = false)
    (hp : preflight p c.machine c.meter = .blocked reason retained) :
    tick p firstResponses c = tick p secondResponses c := by
  rw [tick_blocked stop hp, tick_blocked stop hp]

 theorem commit_work (h : commit p responses s m = some next) :
    next.meter.fuel = m.fuel ∧ next.meter.tupleFields = m.tupleFields := by
  by_cases na : NotAllocation s.control
  · rw [commit_nonallocation na] at h
    cases hs : step p responses s with
    | none => simp [hs] at h
    | some next => simp only [hs, Option.map_some, Option.some.injEq] at h; cases h; exact finish_work
  · rcases s with ⟨control, a, k, w⟩
    cases control <;> simp only [NotAllocation] at na
    all_goals try contradiction
    case allocate site n init yes no =>
      cases ha : allocate p.profile responses w site n init with
      | mk result after =>
        cases result <;> simp only [commit, ha, Option.some.injEq] at h <;> cases h <;> exact ⟨rfl, rfl⟩

 theorem tick_advanced_work (h : tick p responses c = .advanced next) :
    next.meter.fuel = c.meter.fuel - entryCharge c.machine.control - cellCharge p c.machine ∧
      next.meter.tupleFields = c.meter.tupleFields + tupleCharge c.machine := by
  unfold tick at h
  split at h
  · cases h
  · split at h
    · cases h
    next hp =>
      split at h
      · cases h
      next hc =>
        cases h
        have same := commit_work hc
        rw [preflight_paid hp] at same
        exact same

end ANL.Memory.Tool
