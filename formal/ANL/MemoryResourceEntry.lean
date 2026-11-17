import ANL.MemoryResourceDepth

namespace ANL.Memory.Tool

set_option linter.unusedSimpArgs false

def LocalFrame : Frame → Prop
  | .scope | .callReturn _ _ => False
  | _ => True

/-- Ordinary environment cells are discharged by scope frames or by returning to the saved caller. -/
inductive LocalLayout : Nat → List Frame → Prop where
  | nil : LocalLayout 0 []
  | plain : LocalFrame frame → LocalLayout n k → LocalLayout n (frame :: k)
  | scope : LocalLayout n k → LocalLayout (n + 1) (.scope :: k)
  | call : LocalLayout caller.env.length k → LocalLayout n (.callReturn caller loan :: k)

@[simp] theorem local_nil : LocalLayout n [] ↔ n = 0 := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst n; exact .nil

@[simp] theorem local_plain (plain : LocalFrame frame) :
    LocalLayout n (frame :: k) ↔ LocalLayout n k := by
  constructor
  · intro h; cases h
    case plain h next => exact next
    all_goals cases plain
  · exact .plain plain

@[simp] theorem local_scope : LocalLayout (n + 1) (.scope :: k) ↔ LocalLayout n k := by
  constructor
  · intro h; cases h
    case plain bad _ => cases bad
    case scope next => exact next
  · exact .scope

@[simp] theorem local_call : LocalLayout n (.callReturn caller loan :: k) ↔ LocalLayout caller.env.length k := by
  constructor
  · intro h; cases h
    case plain bad _ => cases bad
    case call next => exact next
  · exact .call

 theorem local_pop (h : LocalLayout n (frame :: k)) (plain : LocalFrame frame) : LocalLayout n k :=
  (local_plain plain).mp h

 theorem local_preservation (hs : Step p responses s next) (safe : next.control ≠ .invalid)
    (h : LocalLayout s.current.env.length s.kont) : LocalLayout next.current.env.length next.kont := by
  cases hs
  all_goals try { exact False.elim (safe rfl) }
  all_goals try { simp_all [LocalFrame] }
  all_goals try { exact .plain trivial h }
  all_goals try { exact local_pop h trivial }
  all_goals try { exact .plain trivial (local_pop h trivial) }
  all_goals try { exact .scope (local_pop h trivial) }

  case call t f args a k w =>
    cases args with
    | nil => exact h
    | cons e rest => exact .plain trivial h
  case callView i binding t f mode args a k w found permission =>
    cases args with
    | nil => exact h
    | cons e rest => exact .plain trivial h
  case argumentReturn value a f loan rest values k w =>
    cases rest with
    | nil => exact local_pop h trivial
    | cons e rest => exact .plain trivial (local_pop h trivial)
  case assignReturn i v env a k w updated =>
    change LocalLayout env.length k
    rw [env_update_length updated]
    exact local_pop h trivial
  case lengthFound i binding t a k w found =>
    cases hr : APL.FlatProducts.embedResult (APL.checked (binding.length : Int)) <;> simp only [hr, resume]
    all_goals exact h
  case unaryReturn v a op k w =>
    cases hr : APL.FlatProducts.unary op v <;> simp only [hr, resume]
    all_goals exact local_pop h trivial
  case binaryReturn v a op left k w =>
    cases hr : APL.FlatProducts.binary op left v <;> simp only [hr, resume]
    all_goals exact local_pop h trivial
  case fieldsDone v a values k w =>
    cases hr : APL.FlatProducts.construct (v :: values).reverse <;> simp only [hr, resume]
    all_goals exact local_pop h trivial
  case projectReturn v a i k w =>
    cases hr : APL.FlatProducts.project v i <;> simp only [hr, resume]
    all_goals exact local_pop h trivial

 theorem locals_steps (wf : WellFormedProgram p) (typed : State.Typed p s ty) (steps : Steps p responses s last)
    (h : LocalLayout s.current.env.length s.kont) : LocalLayout last.current.env.length last.kont := by
  induction steps with
  | refl => exact h
  | head step rest ih =>
    have next := preservation wf typed step
    exact ih next (local_preservation step next.not_invalid h)

 theorem entry_locals (wf : WellFormedProgram p) :
    let last := (run p responses budget (initial p fuel)).configuration.machine
    LocalLayout last.current.env.length last.kont :=
  locals_steps wf (entry_typed wf) (run_prefix (c := initial p fuel)) .nil

 theorem entry_normal_reservations (wf : WellFormedProgram p)
    (hr : run p responses budget (initial p fuel) = .completed ⟨⟨.ret value, a, [], w⟩, m⟩) :
    m.slots = 0 ∧ m.liveCells = 0 ∧ a.env = [] ∧ a.resources = [] ∧ w.owners = [] := by
  have path := (run_completed hr).1
  obtain ⟨_, owners, resources, _, _⟩ := normal_entry_cleanup wf path
  have locals := entry_locals (responses := responses) (budget := budget) (fuel := fuel) wf
  simp only [hr, Result.configuration] at locals
  have emptyEnv : a.env = [] := List.length_eq_zero_iff.mp (local_nil.mp locals)
  have account := run_entry_accounted (responses := responses) (budget := budget) (fuel := fuel) wf
  simp only [hr, Result.configuration] at account
  refine ⟨?_, ?_, emptyEnv, resources, owners⟩
  · simpa [logicalSlots, savedSlots, pendingSlots, emptyEnv, resources] using account.2.1
  · simpa [World.liveCells, owners] using account.2.2.1

 theorem entry_event_origin (wf : WellFormedProgram p)
    (member : event ∈ (run p responses budget (initial p fuel)).configuration.machine.world.trace) :
    ∃ fn, p.functions[event.site.function]? = some fn ∧ fn.id = event.site.function ∧
      event.site.heap < fn.body.heapSites.length := entry_event_site wf (run_prefix (c := initial p fuel)) member

 theorem start_iff : start? p fuel = some c ↔ fuel ≤ maxFuel ∧ c = initial p fuel := by
  unfold start?
  split <;> simp_all [eq_comm]
  omega

end ANL.Memory.Tool
