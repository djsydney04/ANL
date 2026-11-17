import APL.LoopGenerationComplete

/-! Explicit sufficient heights uniform over symbolic contents, incoming paths
and fresh counters, including a single height for the finite function table.
These unbounded-model results do not certify production resource limits. -/

namespace APL.LoopGeneration
open VCG LoopVCG LoopAnnotations

/-- Syntax/body-expansion height; unrelated to execution iterations or fuel. -/
def sufficientHeight (fs : Functions) (ceiling : Nat) (e : Term) : Nat :=
  ceiling * bodyBound fs + nodes e + 1

theorem uniform_generation
    (wf : WellTyped fs) (hp : PreconditionsTyped fs preconditions) (ranked : Ranked fs rank)
    (ht : LoopAnnotations.HasType (signatures fs) Γ e ty) (hr : CallsBelow rank ceiling e) :
    ∀ env path start, env.length = Γ.length →
      ∃ generated, analyze fs preconditions (sufficientHeight fs ceiling e) Γ e env path start = some generated ∧
        Shape Γ.length generated := by
  intro env path start hlen
  exact analyze_complete wf hp ranked ht hr hlen (Nat.lt_succ_self _)

theorem exists_uniform_height
    (wf : WellTyped fs) (hp : PreconditionsTyped fs preconditions) (ranked : Ranked fs rank)
    (ht : LoopAnnotations.HasType (signatures fs) Γ e ty) (hr : CallsBelow rank ceiling e) :
    ∃ height, ∀ env path start, env.length = Γ.length →
      ∃ generated, analyze fs preconditions height Γ e env path start = some generated ∧
        Shape Γ.length generated :=
  ⟨sufficientHeight fs ceiling e, uniform_generation wf hp ranked ht hr⟩

theorem function_generation
    (wf : WellTyped fs) (hp : PreconditionsTyped fs preconditions) (ranked : Ranked fs rank)
    (lookup : fs[f]? = some fn) (hlen : env.length = fn.params.length) :
    ∃ generated, analyze fs preconditions (sufficientHeight fs (rank f) fn.body)
        (LocalState.immutable fn.params.reverse) fn.body env path start = some generated ∧
      Shape fn.params.length generated := by
  have he : env.length = (LocalState.immutable fn.params.reverse).length := by
    simpa [LocalState.immutable] using hlen
  have h := uniform_generation wf hp ranked (wf f fn lookup) (ranked f fn lookup) env path start he
  simpa [LocalState.immutable] using h

def rankBound (fs : Functions) (rank : Nat → Nat) : Nat :=
  1 + ((List.range fs.size).map rank).sum

theorem rank_bounded {fs : Functions} {fn : Function} {rank : Nat → Nat}
    (lookup : fs[f]? = some fn) : rank f < rankBound fs rank := by
  have index := (Array.getElem?_eq_some_iff.mp lookup).1
  have bound := member_sum_bound (xs := (List.range fs.size).map rank)
    (List.mem_map.mpr ⟨f, List.mem_range.mpr index, rfl⟩)
  unfold rankBound
  omega

/-- One uniform height works for every function in the finite table and every
symbolic environment of its parameter length, regardless of symbol contents,
path, or initial fresh counter. Rank existence/extraction is not asserted. -/
theorem table_uniform_height
    (wf : WellTyped fs) (hp : PreconditionsTyped fs preconditions) (ranked : Ranked fs rank) :
    ∃ height, ∀ (f : Nat) (fn : Function), fs[f]? = some fn → ∀ env path start, env.length = fn.params.length →
      ∃ generated, analyze fs preconditions height (LocalState.immutable fn.params.reverse)
        fn.body env path start = some generated ∧ Shape fn.params.length generated := by
  refine ⟨rankBound fs rank * bodyBound fs + bodyBound fs + 1, ?_⟩
  intro f fn lookup env path start hlen
  have he : env.length = (LocalState.immutable fn.params.reverse).length := by
    simpa [LocalState.immutable] using hlen
  have rankLe := Nat.mul_le_mul_right (bodyBound fs) (Nat.le_of_lt (rank_bounded (rank := rank) lookup))
  have sizeLt := body_bounded lookup
  have enough : rank f * bodyBound fs + nodes fn.body < rankBound fs rank * bodyBound fs + bodyBound fs + 1 := by omega
  have h := analyze_complete (path := path) (start := start) wf hp ranked (wf f fn lookup) (ranked f fn lookup) he enough
  simpa [LocalState.immutable] using h

end APL.LoopGeneration
