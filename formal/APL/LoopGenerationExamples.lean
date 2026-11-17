import APL.LoopGenerationCorollaries

/-! Kernel-checked generation boundaries: shared and dead calls, typed undefined
annotations, arbitrary symbolic inputs, and successful generation paired with
an actual infinite machine execution. -/

namespace APL.LoopGeneration.Examples
open VCG LoopVCG LoopAnnotations

private def undefined : Assertion :=
  .binary .eq (.binary .div (.lit (.int 1)) (.lit (.int 0))) (.lit (.int 0))
private theorem undefined_typed : Assertion.HasType Γ undefined .bool :=
  .binary (.binary .lit .lit rfl) .lit rfl

private def first : Function := ⟨"first", [.bool, .bool], .bool, .local 1⟩
private def copy : Function := ⟨"copy", [.bool], .bool, .call 0 [.local 0, .local 0]⟩
private def shared : Function := ⟨"shared", [.bool], .bool,
  .call 0 [.call 1 [.local 0], .call 1 [.lit (.bool false)]]⟩
private def disconnected : Function := ⟨"disconnected", [], .unit,
  .whileE [.lit (.bool false), undefined] (.lit (.bool true)) (.lit .unit)⟩
private def table : Functions := #[first, copy, shared, disconnected]
private def pre : Preconditions := fun _ => [.lit (.bool false), undefined.toSpec]

private theorem signature0 : (signatures table)[0]? = some ([Ty.bool, Ty.bool], Ty.bool) := by
  simp [signatures, table, first, copy, shared, disconnected]
private theorem signature1 : (signatures table)[1]? = some ([Ty.bool], Ty.bool) := by
  simp [signatures, table, first, copy, shared, disconnected]
private theorem signature2 : (signatures table)[2]? = some ([Ty.bool], Ty.bool) := by
  simp [signatures, table, first, copy, shared, disconnected]

private theorem table_typed : WellTyped table := by
  intro f fn lookup
  rcases f with _ | (_ | (_ | (_ | f)))
  · have eq : fn = first := Option.some.inj lookup.symm
    subst fn
    exact .local rfl
  · have eq : fn = copy := Option.some.inj lookup.symm
    subst fn
    exact .call signature0 (.cons (.local rfl) (.cons (.local rfl) .nil))
  · have eq : fn = shared := Option.some.inj lookup.symm
    subst fn
    exact .call signature0 (.cons (.call signature1 (.cons (.local rfl) .nil))
      (.cons (.call signature1 (.cons .lit .nil)) .nil))
  · have eq : fn = disconnected := Option.some.inj lookup.symm
    subst fn
    apply LoopAnnotations.HasType.whileE (by decide)
    · intro a member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .lit
      · exact undefined_typed
    · exact .lit
    · exact .lit
  · simp [table] at lookup

private theorem pre_typed : PreconditionsTyped table pre := by
  intro f fn lookup clause member
  simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .lit
  · exact .binary (.binary .lit .lit rfl) .lit rfl

private theorem table_ranked : Ranked table id := by
  intro f fn lookup
  rcases f with _ | (_ | (_ | (_ | f)))
  · have eq : fn = first := Option.some.inj lookup.symm
    subst fn
    trivial
  · have eq : fn = copy := Option.some.inj lookup.symm
    subst fn
    simp [CallsBelow, ArgumentsBelow, copy, id]
  · have eq : fn = shared := Option.some.inj lookup.symm
    subst fn
    simp [CallsBelow, ArgumentsBelow, shared, id]
  · have eq : fn = disconnected := Option.some.inj lookup.symm
    subst fn
    trivial
  · simp [table] at lookup

/-- Shared callees, declaration-order parameters and disconnected functions all
share one generation bound even with false/undefined but typed preconditions. -/
private theorem dag_uniform :
    ∃ height, ∀ (f : Nat) (fn : Function), table[f]? = some fn → ∀ env path start,
      env.length = fn.params.length →
      ∃ generated, analyze table pre height (LocalState.immutable fn.params.reverse)
        fn.body env path start = some generated ∧ Shape fn.params.length generated :=
  table_uniform_height table_typed pre_typed table_ranked

private def nested : Term :=
  .letMut (.lit (.bool true))
    (.whileE [.lit (.bool true)]
      (.letE (.assign 0 (.lit (.bool false)))
        (.call 2 [.local 1]))
      (.whileE [.lit (.bool false), undefined] (.lit (.bool false)) (.lit .unit)))

private theorem nested_typed : LoopAnnotations.HasType (signatures table) [] nested .unit := by
  apply LoopAnnotations.HasType.letMut .lit
  apply LoopAnnotations.HasType.whileE (by decide)
  · intro a member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst a
    exact .lit
  · exact .letE (.assign rfl .lit) (.call signature2 (.cons (.local rfl) .nil))
  · apply LoopAnnotations.HasType.whileE (by decide)
    · intro a member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .lit
      · exact undefined_typed
    · exact .lit
    · exact .lit

/-- Calls in an effectful condition and nested loop bodies are generated once
symbolically. Neither false nor undefined typed invariants block generation. -/
private theorem nested_effectful_condition : ∀ path start,
    ∃ generated, analyze table pre (sufficientHeight table 3 nested) [] nested [] path start = some generated ∧
      Shape 0 generated := by
  intro path start
  exact uniform_generation table_typed pre_typed table_ranked nested_typed
    (by simp [CallsBelow, ArgumentsBelow, nested, id] : CallsBelow id 3 nested) [] path start rfl

/-- Arbitrary symbols and aliased fresh counters still generate. This gives no
operational safety conclusion without the separate support/validity premises. -/
private theorem arbitrary_symbol_contents : ∃ generated,
    analyze table pre (sufficientHeight table 2 shared.body)
      (LocalState.immutable [.bool]) shared.body [.var 100000] (.truth false) 0 = some generated := by
  obtain ⟨generated, hg, _⟩ := function_generation table_typed pre_typed table_ranked
    (f := 2) (fn := shared) rfl (env := [.var 100000]) (path := .truth false) (start := 0) rfl
  exact ⟨generated, hg⟩

private def deadRecursion : Function := ⟨"dead", [], .unit,
  .ifE (.lit (.bool false)) (.call 0 []) (.lit .unit)⟩

/-- Rank coverage cannot ignore the unreachable branch. -/
private theorem dead_recursive_rank_impossible : ¬ ∃ rank, Ranked #[deadRecursion] rank := by
  rintro ⟨rank, ranked⟩
  have h := ranked 0 deadRecursion rfl
  change True ∧ (rank 0 < rank 0 ∧ True) ∧ True at h
  omega

private def cycleA : Function := ⟨"a", [], .unit, .call 1 []⟩
private def cycleB : Function := ⟨"b", [], .unit, .call 0 []⟩

private theorem mutual_rank_impossible : ¬ ∃ rank, Ranked #[cycleA, cycleB] rank := by
  rintro ⟨rank, ranked⟩
  have a := ranked 0 cycleA rfl
  have b := ranked 1 cycleB rfl
  change rank 1 < rank 0 ∧ True at a
  change rank 0 < rank 1 ∧ True at b
  omega

private def forever : Term := .whileE [.lit (.bool true)] (.lit (.bool true)) (.lit .unit)
private theorem forever_typed : LoopAnnotations.HasType (signatures (#[] : Functions)) [] forever .unit := by
  apply LoopAnnotations.HasType.whileE (by decide)
  · intro a member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst a
    exact .lit
  · exact .lit
  · exact .lit

/-- Successful syntactic generation does not make the loop a finite execution. -/
private theorem divergent_syntax_generates : ∃ generated,
    analyze #[] (fun _ => []) (sufficientHeight #[] 0 forever) [] forever [] (.truth true) 0 = some generated := by
  have wf : WellTyped (#[] : Functions) := by intro f fn h; simp at h
  have pt : PreconditionsTyped #[] (fun _ => []) := by intro f fn h; simp at h
  have rk : Ranked #[] (fun _ => 0) := by intro f fn h; simp at h
  obtain ⟨generated, hg, _⟩ := uniform_generation wf pt rk forever_typed
    (by trivial : CallsBelow (fun _ => 0) 0 forever) [] (.truth true) 0 rfl
  exact ⟨generated, hg⟩

private theorem condition_cycle_run (budget : Nat) :
    LocalState.run #[] budget (.eval (.lit (.bool true)) []
      [.condition (.lit (.bool true)) (.lit .unit)]) = none := by
  induction budget using Nat.strongRecOn with
  | ind budget ih =>
    rcases budget with _ | (_ | (_ | (_ | budget)))
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ih budget (by omega)

/-- The same term has no completed actual-machine run at any finite budget. -/
private theorem divergent_run_all_budgets (budget : Nat) :
    LocalState.run #[] budget (.eval forever.erase [] []) = none := by
  simp only [forever, Term.erase]
  cases budget with
  | zero => rfl
  | succ budget => exact condition_cycle_run budget

private theorem generation_does_not_imply_return :
    (∃ generated, analyze #[] (fun _ => []) (sufficientHeight #[] 0 forever)
      [] forever [] (.truth true) 0 = some generated) ∧
    (∀ budget, LocalState.run #[] budget (.eval forever.erase [] []) = none) :=
  ⟨divergent_syntax_generates, divergent_run_all_budgets⟩

end APL.LoopGeneration.Examples

namespace APL.LoopGeneration.Examples
open VCG LoopVCG LoopAnnotations

private def poison : SymTerm := .binary .div (.var 0) (.lit (.int 0))
private def loop : Term := .whileE [.local 0] (.local 0) (.lit .unit)

/-- Syntactic generation needs neither denotation nor a fresh-counter support
bound: this incoming Boolean cell is undefined in every model and mentions the
same ID that the mutable head will allocate from counter zero. -/
private theorem undefined_incoming_symbol_still_generates :
    (∀ model, poison.eval model = none) ∧
    ¬ SymbolsBelow 0 [poison] ∧
    ∃ generated, analyze #[] (fun _ => []) (sufficientHeight #[] 0 loop)
      [(.bool, true)] loop [poison] (.truth true) 0 = some generated ∧ Shape 1 generated := by
  refine ⟨?_, ?_, ?_⟩
  · intro model
    cases h : model 0 <;> simp [poison, SymTerm.eval, h, mShort, mBinary]
  · simp [SymbolsBelow, Below, poison]
  · have wf : WellTyped (#[] : Functions) := by intro f fn h; simp at h
    have hp : PreconditionsTyped #[] (fun _ => []) := by intro f fn h; simp at h
    have ranked : Ranked #[] (fun _ => 0) := by intro f fn h; simp at h
    have typed : LoopAnnotations.HasType (signatures (#[] : Functions)) [(.bool, true)] loop .unit := by
      apply LoopAnnotations.HasType.whileE (by decide)
      · intro clause member
        simp only [List.mem_singleton] at member
        subst clause
        exact .local rfl
      · exact .local rfl
      · exact .lit
    exact uniform_generation wf hp ranked typed
      (by trivial : CallsBelow (fun _ => 0) 0 loop) [poison] (.truth true) 0 rfl

private def dead : Function := ⟨"dead", [], .unit,
  .whileE [.lit (.bool true)] (.lit (.bool false)) (.call 1 [.call 0 []])⟩
private def identity : Function := ⟨"identity", [.unit], .unit, .local 0⟩

/-- Even an argument call in the body of a literal-false loop must decrease the
rank. Omitting either while-body traversal or argument traversal loses this. -/
private theorem recursion_in_dead_loop_argument_has_no_rank :
    ¬ ∃ rank, Ranked #[dead, identity] rank := by
  rintro ⟨rank, ranked⟩
  have h := ranked 0 dead rfl
  change True ∧ (rank 1 < rank 0 ∧ (rank 0 < rank 0 ∧ True) ∧ True) at h
  omega

end APL.LoopGeneration.Examples
