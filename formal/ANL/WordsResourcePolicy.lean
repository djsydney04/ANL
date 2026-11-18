import ANL.WordsResources

namespace ANL.Words.Tool

open ANL.Memory

set_option linter.unusedSimpArgs false

def entryCharge : Control → Nat
  | .eval _ => 1
  | _ => 0

def slotCharge (p : Program) (s : State) : Nat :=
  match s.control with
  | .eval (.call _ _ args) => args.length
  | .eval (.callView _ _ _ _ args) => args.length + 1
  | .ret _ => match s.kont with | .bind _ _ :: _ => 1 | _ => 0
  | .allocate _ n _ _ _ => if n ≤ p.profile.maxCells then 1 else 0
  | _ => 0

def cellCharge (p : Program) (s : State) : Nat :=
  match s.control with
  | .allocate _ n _ _ _ => if n ≤ p.profile.maxCells then n else 0
  | _ => 0

def tupleCharge (s : State) : Nat :=
  match s.control with
  | .ret value => match s.kont with
    | .fields [] prior :: _ => match value with
      | .scalar _ => prior.length + 1
      | _ => 0
    | _ => 0
  | _ => 0

def paid (p : Program) (s : State) (m : Meter) : Meter :=
  {m with
    fuel := m.fuel - entryCharge s.control - cellCharge p s,
    slots := m.slots + slotCharge p s, liveCells := m.liveCells + cellCharge p s,
    tupleFields := m.tupleFields + tupleCharge s}

 theorem enter_allowed (h : enter m = .allowed next) :
    m.depth < maxDepth ∧ 0 < m.fuel ∧ next = {m with fuel := m.fuel - 1} := by
  unfold enter at h
  split at h
  next hd =>
    split at h
    next hf => cases h; exact ⟨hd, hf, rfl⟩
    · cases h
  · cases h

 theorem reserveSlots_allowed (h : reserveSlots m count = .allowed next) :
    m.slots + count ≤ maxSlots ∧ next = {m with slots := m.slots + count} := by
  unfold reserveSlots at h; split at h
  next bound => cases h; exact ⟨bound, rfl⟩
  · cases h

 theorem reserveOwner_allowed (h : reserveOwner m n = .allowed next) :
    m.liveCells + n ≤ maxLiveCells ∧ m.slots + 1 ≤ maxSlots ∧ n ≤ m.fuel ∧
      next = {m with liveCells := m.liveCells + n, slots := m.slots + 1, fuel := m.fuel - n} := by
  unfold reserveOwner at h
  split at h
  next hc =>
    split at h
    next hs =>
      split at h
      next hf => cases h; exact ⟨hc, hs, hf, rfl⟩
      · cases h
    · cases h
  · cases h

 theorem reserveTuple_allowed (h : reserveTuple m n = .allowed next) :
    m.tupleFields + n ≤ maxTupleFields ∧ next = {m with tupleFields := m.tupleFields + n} := by
  unfold reserveTuple at h; split at h
  next bound => cases h; exact ⟨bound, rfl⟩
  · cases h

 theorem preflight_paid (h : preflight p s m = .allowed next) : next = paid p s m := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp only [preflight] at h
  case eval term =>
    cases he : enter m with
    | blocked reason retained => rw [he] at h; cases h
    | allowed entered =>
      rw [he] at h
      obtain ⟨_, _, rfl⟩ := enter_allowed he
      cases term <;> simp only at h
      all_goals try { cases h; rfl }
      all_goals obtain ⟨_, rfl⟩ := reserveSlots_allowed h; rfl
  case ret value =>
    cases k with
    | nil => cases h; rfl
    | cons frame rest =>
      cases frame <;> try simp only at h
      all_goals try { cases h; rfl }
      case bind mutable body => obtain ⟨_, rfl⟩ := reserveSlots_allowed h; rfl
      case fields remaining prior =>
        cases remaining <;> cases value <;> simp only at h
        all_goals try { cases h; rfl }
        obtain ⟨_, rfl⟩ := reserveTuple_allowed h
        rfl
  case allocate site n init yes no =>
    split at h
    next eligible =>
      obtain ⟨_, _, _, rfl⟩ := reserveOwner_allowed h
      simp [paid, slotCharge, cellCharge, tupleCharge, entryCharge, eligible]
    next rejected => cases h; simp [paid, slotCharge, cellCharge, tupleCharge, entryCharge, rejected]
  all_goals cases h; rfl

 theorem preflight_parents (h : preflight p s m = .allowed next) : next.parents = m.parents := by
  rw [preflight_paid h]; rfl

 theorem preflight_depth (h : preflight p s m = .allowed next) : next.depth = m.depth := by
  rw [preflight_paid h]; rfl

 theorem reserveOwner_blocked_atomic (h : reserveOwner m n = .blocked reason retained) : retained = m := by
  unfold reserveOwner at h
  split at h
  · split at h
    · split at h <;> cases h <;> rfl
    · cases h; rfl
  · cases h; rfl

 theorem zero_owner (bound : m.liveCells ≤ maxLiveCells) :
    reserveOwner m 0 = reserveSlots m 1 := by simp [reserveOwner, reserveSlots, bound]

 theorem depth_before_fuel (h : maxDepth ≤ m.depth) : enter m = .blocked .depth m := by
  simp [enter, show ¬m.depth < maxDepth by omega]

 theorem expression_fuel (depth : m.depth < maxDepth) (fuel : m.fuel = 0) :
    enter m = .blocked .expressionFuel m := by simp [enter, depth, fuel]

 theorem eligible_allocation (h : preflight p ⟨.allocate site n init yes no, a, k, w⟩ m = .allowed next)
    (eligible : n ≤ p.profile.maxCells) :
    m.liveCells + n ≤ maxLiveCells ∧ m.slots + 1 ≤ maxSlots ∧ n ≤ m.fuel := by
  simp only [preflight, eligible, ↓reduceIte] at h
  exact ⟨(reserveOwner_allowed h).1, (reserveOwner_allowed h).2.1, (reserveOwner_allowed h).2.2.1⟩

 theorem rejected_allocation (h : p.profile.maxCells < n) :
    preflight p ⟨.allocate site n init yes no, a, k, w⟩ m = .allowed m := by
  simp [preflight, show ¬n ≤ p.profile.maxCells by omega]

def Preflight.meter : Preflight → Meter
  | .allowed m | .blocked _ m => m

 theorem enter_bounded (h : m.Bounded) : (enter m).meter.Bounded := by
  unfold enter
  split
  · split <;> exact h
  · exact h

 theorem slots_bounded (h : m.Bounded) : (reserveSlots m n).meter.Bounded := by
  unfold reserveSlots
  split
  next bound => exact ⟨bound, h.2⟩
  · exact h

 theorem owner_bounded (h : m.Bounded) : (reserveOwner m n).meter.Bounded := by
  unfold reserveOwner
  split
  next cells =>
    split
    next slots =>
      split
      · exact ⟨slots, cells, h.2.2⟩
      · exact h
    · exact h
  · exact h

 theorem tuple_bounded (h : m.Bounded) : (reserveTuple m n).meter.Bounded := by
  unfold reserveTuple
  split
  next bound => exact ⟨h.1, h.2.1, bound⟩
  · exact h

 theorem preflight_bounded (h : m.Bounded) : (preflight p s m).meter.Bounded := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp only [preflight]
  case eval term =>
    have bounded := enter_bounded h
    cases he : enter m with
    | blocked reason retained => simpa [he, Preflight.meter] using bounded
    | allowed entered =>
      have hb : entered.Bounded := by simpa [he, Preflight.meter] using bounded
      cases term <;> try exact hb
      all_goals exact slots_bounded hb
  case ret value =>
    cases k with
    | nil => exact h
    | cons frame rest =>
      cases frame <;> try exact h
      case bind => exact slots_bounded h
      case fields remaining prior =>
        cases remaining <;> cases value <;> try exact h
        exact tuple_bounded h
  case allocate => split; exact owner_bounded h; exact h
  all_goals exact h

 theorem release_bounded {m : Meter} (h : m.Bounded) : (m.release slots cells).Bounded := by
  exact ⟨Nat.le_trans (Nat.sub_le _ _) h.1, Nat.le_trans (Nat.sub_le _ _) h.2.1, h.2.2⟩

 theorem finish_bounded (h : m.Bounded) : (finish s next m).Bounded := by
  unfold finish
  split
  · exact h
  · split
    · split <;> try exact h
      all_goals split <;> exact h
    · split <;> try exact h
      · exact release_bounded h
      all_goals split <;> exact h
    · split <;> exact h
    · split <;> exact h
    · exact h
    · exact release_bounded h
    · exact release_bounded h
    · exact h

 def Meter.reservations (m : Meter) := (m.slots, m.liveCells, m.tupleFields, m.depth, m.parents)

 theorem enter_blocked (h : enter m = .blocked reason retained) : retained = m := by
  unfold enter at h
  split at h
  · split at h <;> cases h <;> rfl
  · cases h; rfl

 theorem slots_blocked (h : reserveSlots m count = .blocked reason retained) : retained = m := by
  unfold reserveSlots at h; split at h <;> cases h <;> rfl

 theorem tuple_blocked (h : reserveTuple m count = .blocked reason retained) : retained = m := by
  unfold reserveTuple at h; split at h <;> cases h <;> rfl

 theorem preflight_blocked_reservations (h : preflight p s m = .blocked reason retained) :
    retained.reservations = m.reservations := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp only [preflight] at h
  case eval term =>
    cases he : enter m with
    | blocked why before =>
      rw [he] at h
      cases h
      rw [enter_blocked he]
    | allowed entered =>
      rw [he] at h
      obtain ⟨_, _, rfl⟩ := enter_allowed he
      cases term <;> simp only at h
      all_goals try { cases h }
      all_goals rw [slots_blocked h]; rfl
  case ret value =>
    cases k with
    | nil => cases h
    | cons frame rest =>
      cases frame <;> try simp only at h
      all_goals try { cases h }
      case bind => rw [slots_blocked h]
      case fields remaining prior =>
        cases remaining <;> cases value <;> simp only at h
        all_goals try { cases h }
        rw [tuple_blocked h]
  case allocate =>
    split at h
    · rw [reserveOwner_blocked_atomic h]
    · cases h
  all_goals cases h

 theorem finish_work : (finish s next m).fuel = m.fuel ∧ (finish s next m).tupleFields = m.tupleFields := by
  unfold finish
  split
  · exact ⟨rfl, rfl⟩
  · split
    · split <;> try exact ⟨rfl, rfl⟩
      all_goals split <;> exact ⟨rfl, rfl⟩
    · split <;> try exact ⟨rfl, rfl⟩
      all_goals split <;> exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩
    all_goals exact ⟨rfl, rfl⟩

 theorem expression_entry_prepaid
    (h : preflight p ⟨.eval term, a, k, w⟩ m = .allowed next) :
    m.depth < maxDepth ∧ 0 < m.fuel ∧ next.fuel = m.fuel - 1 := by
  have fields := preflight_paid h
  simp only [preflight] at h
  cases he : enter m with
  | blocked reason retained => rw [he] at h; cases h
  | allowed entered =>
    have guards := enter_allowed he
    refine ⟨guards.1, guards.2.1, ?_⟩
    rw [fields]
    rfl

end ANL.Words.Tool
