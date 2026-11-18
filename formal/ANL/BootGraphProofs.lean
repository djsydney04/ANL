import ANL.BootGraph

namespace ANL.Boot

inductive CallPath (p : Program) : Nat → List Nat → Prop where
  | nil : CallPath p f []
  | cons : Edge p f g → CallPath p g rest → CallPath p f (g :: rest)

theorem CallPath.reaches_member (path : CallPath p f rest) (mem : g ∈ rest) :
    ∃ n, 0 < n ∧ Reach p n f g := by
  induction path with
  | nil => contradiction
  | cons edge tail ih =>
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact ⟨1, by decide, .step edge .refl⟩
    · obtain ⟨n, positive, reach⟩ := ih mem
      exact ⟨n + 1, by omega, .step edge reach⟩

theorem CallPath.nodup (free : CycleFree p) (path : CallPath p f rest) : (f :: rest).Nodup := by
  induction path with
  | nil => simp
  | cons edge tail ih =>
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    intro mem
    obtain ⟨n, positive, cycle⟩ := (CallPath.cons edge tail).reaches_member mem
    exact free _ _ positive cycle

theorem CallPath.member_bound (path : CallPath p f rest) (mem : g ∈ rest) : g < p.functions.length := by
  induction path with
  | nil => contradiction
  | cons edge _ ih =>
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact edge.target_bound
    · exact ih mem

theorem Reach.callPath (reach : Reach p n f g) : ∃ rest, CallPath p f rest ∧ rest.length = n := by
  induction reach with
  | refl => exact ⟨[], .nil, rfl⟩
  | step edge _ ih =>
    obtain ⟨rest, path, length⟩ := ih
    exact ⟨_ :: rest, .cons edge path, by simp [length]⟩

theorem CycleFree.acyclic (free : CycleFree p) : Acyclic p := by
  intro f bound n g reach
  obtain ⟨rest, path, length⟩ := reach.callPath
  have subset : f :: rest ⊆ List.range p.functions.length := by
    intro x mem
    simp only [List.mem_range]
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact bound
    · exact path.member_bound mem
  have finite := (path.nodup free).length_le_of_subset subset
  simp only [List.length_cons, List.length_range, length] at finite
  omega

theorem acyclic_iff_cycleFree : Acyclic p ↔ CycleFree p :=
  ⟨Acyclic.no_cycle, CycleFree.acyclic⟩

theorem checkGraph_cycleFree_iff : checkGraph p = true ↔ CycleFree p :=
  checkGraph_iff.trans acyclic_iff_cycleFree

end ANL.Boot
