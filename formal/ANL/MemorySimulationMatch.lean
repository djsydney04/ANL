import ANL.MemorySimulationPlacement

namespace ANL.Memory.Simulation
open Lowering

/-- Actual target prefix, concrete next relation, and a strict rank for source-only work. -/
def Matched (p : Program) (q : Mir.Program) (responses : Responses)
    (source : ANL.Memory.State) (target : Mir.State) (next : ANL.Memory.State) : Prop :=
  ∃ count targetNext, MirStepsN q responses count target targetNext ∧ Related p next targetNext ∧
    (count = 0 → coreRank next < coreRank source)

theorem Matched.silent (silent : CoreSilent p responses source next) (related : Related p next target) :
    Matched p q responses source target next := ⟨0, target, .zero, related, fun _ => silent.rank⟩

theorem Matched.positive (path : MirStepsN q responses count target targetNext) (positive : count ≠ 0)
    (related : Related p next targetNext) : Matched p q responses source target next :=
  ⟨count, targetNext, path, related, fun zero => False.elim (positive zero)⟩

theorem MirStepsN.trans (left : MirStepsN p responses m first middle)
    (right : MirStepsN p responses n middle last) : MirStepsN p responses (n + m) first last := by
  induction left with
  | zero => simpa using right
  | succ hs rest ih => simpa [Nat.add_assoc] using MirStepsN.succ hs (ih right)

theorem Matched.prepend (path : MirStepsN q responses count first middle)
    (matched : Matched p q responses source middle next) : Matched p q responses source first next := by
  obtain ⟨n, last, tail, related, decreased⟩ := matched
  refine ⟨n + count, last, path.trans tail, related, ?_⟩
  intro zero
  exact decreased (by omega)

theorem resume_related {code : KontCode offset locals ids k (.returned mk) captures}
    (h : Placed p code before after source target) (valid : result ≠ APL.FlatProducts.Result.invalid) :
    Related p (ANL.Memory.resume result source k world) (Mir.resume result target mk world) := by
  cases result with
  | value value => exact .ret code h .returned
  | trap kind => exact .trap code h
  | invalid => exact False.elim (valid rfl)

theorem resume_valid_of_typed (typed : State.Typed p (ANL.Memory.resume result source k world) ty) :
    result ≠ APL.FlatProducts.Result.invalid := by
  intro invalid
  subst result
  exact typed.not_invalid rfl

end ANL.Memory.Simulation
