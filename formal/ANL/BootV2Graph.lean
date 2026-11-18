import ANL.BootV2Policy

namespace ANL.Boot.V2

def Program.definedAt (p : Program) (f : Nat) : Bool :=
  match p.functions[f]? with | some (.defined _) => true | _ => false

def Program.successors (p : Program) (f : Nat) : List Nat :=
  match p.functions[f]? with
  | some (.defined d) => (calls d.function.body).filter p.definedAt
  | _ => []

inductive Edge (p : Program) (f g : Nat) : Prop where
  | intro : p.functions[f]? = some (.defined source) →
      p.functions[g]? = some (.defined target) → g ∈ calls source.function.body → Edge p f g

inductive Reach (p : Program) : Nat → Nat → Nat → Prop where
  | refl : Reach p 0 f f
  | step : Edge p f g → Reach p n g h → Reach p (n + 1) f h

/-- Every finite defined-call path fits inside the finite declaration table. -/
def PathBound (p : Program) (limit f : Nat) : Prop :=
  ∀ n g, Reach p n f g → n < limit

def Acyclic (p : Program) : Prop :=
  ∀ f < p.functions.length, PathBound p p.functions.length f

def CycleFree (p : Program) : Prop :=
  ∀ f n, 0 < n → ¬ Reach p n f f

/-- One shared vector per round avoids recursive rechecking of a call diamond. -/
def graphLevels (p : Program) : Nat → List Bool
  | 0 => List.replicate p.functions.length false
  | n + 1 =>
    let previous := graphLevels p n
    (List.range p.functions.length).map fun f =>
      (p.successors f).all (fun g => (previous[g]?).getD false)

def checkGraph (p : Program) : Bool :=
  (graphLevels p p.functions.length).all id

theorem edge_iff : Edge p f g ↔ g ∈ p.successors f := by
  constructor
  · rintro ⟨hf, hg, mem⟩
    simp [Program.successors, Program.definedAt, hf, hg, mem]
  · intro h
    unfold Program.successors at h
    split at h
    next d hf =>
      obtain ⟨mem, good⟩ := List.mem_filter.mp h
      unfold Program.definedAt at good
      split at good
      next target hg => exact .intro hf hg mem
      next => contradiction
    next => contradiction

theorem Edge.source_bound (edge : Edge p f g) : f < p.functions.length := by
  cases edge with
  | intro hf _ _ => exact List.getElem?_eq_some_iff.mp hf |>.1

theorem Edge.target_bound (edge : Edge p f g) : g < p.functions.length := by
  cases edge with
  | intro _ hg _ => exact List.getElem?_eq_some_iff.mp hg |>.1

theorem pathBound_zero : ¬ PathBound p 0 f := by
  intro h
  have := h 0 f .refl
  omega

theorem pathBound_succ : PathBound p (n + 1) f ↔ ∀ g ∈ p.successors f, PathBound p n g := by
  constructor
  · intro bound g mem k target path
    have := bound (k + 1) target (.step (edge_iff.mpr mem) path)
    omega
  · intro next k target path
    cases path with
    | refl => omega
    | step edge path =>
      have := next _ (edge_iff.mp edge) _ _ path
      omega

theorem graphLevels_length : (graphLevels p n).length = p.functions.length := by
  cases n <;> simp [graphLevels]

theorem graphLevels_iff (hf : f < p.functions.length) :
    (graphLevels p n)[f]?.getD false = true ↔ PathBound p n f := by
  induction n generalizing f with
  | zero => simp [graphLevels, hf, pathBound_zero]
  | succ n ih =>
    simp only [graphLevels, List.getElem?_map, List.getElem?_range hf, Option.map_some,
      Option.getD_some, List.all_eq_true, pathBound_succ]
    constructor
    · intro h g mem
      exact (ih (edge_iff.mpr mem).target_bound).mp (h g mem)
    · intro h g mem
      exact (ih (edge_iff.mpr mem).target_bound).mpr (h g mem)

theorem checkGraph_iff : checkGraph p = true ↔ Acyclic p := by
  simp only [checkGraph, List.all_eq_true, id_eq, Acyclic]
  constructor
  · intro h f hf
    apply (graphLevels_iff hf).mp
    have hg : f < (graphLevels p p.functions.length).length := by simpa [graphLevels_length] using hf
    rw [List.getElem?_eq_getElem hg, Option.getD_some]
    exact h _ (List.getElem_mem hg)
  · intro h b mem
    obtain ⟨f, hf, eq⟩ := List.getElem_of_mem mem
    have bound : f < p.functions.length := by simpa [graphLevels_length] using hf
    have good := (graphLevels_iff (n := p.functions.length) bound).mpr (h f bound)
    simpa [List.getElem?_eq_getElem hf, eq] using good

theorem Reach.append (first : Reach p n f g) (second : Reach p m g h) :
    Reach p (n + m) f h := by
  induction first with
  | refl => simpa using second
  | step edge _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Reach.step edge (ih second)

theorem Reach.repeat (cycle : Reach p n f f) (k : Nat) : Reach p (k * n) f f := by
  induction k with
  | zero => simpa using (Reach.refl (p := p) (f := f))
  | succ k ih => simpa [Nat.succ_mul] using ih.append cycle

theorem Acyclic.no_cycle (h : Acyclic p) : CycleFree p := by
  intro f n positive cycle
  have hf : f < p.functions.length := by
    cases cycle with
    | refl => omega
    | step edge _ => exact edge.source_bound
  have bound := h f hf _ _ (cycle.repeat p.functions.length)
  have lower : p.functions.length ≤ p.functions.length * n := Nat.le_mul_of_pos_right _ positive
  omega

end ANL.Boot.V2
