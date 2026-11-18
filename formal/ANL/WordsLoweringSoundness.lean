import ANL.WordsSimulationEval
import ANL.WordsSimulationReturnStep
import ANL.WordsSimulationClose
import ANL.WordsSimulationCallPhases

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

/-- Every checked core transition matches finitely many actual canonical-MIR transitions.
The zero-transition cases strictly decrease the concrete source syntax/continuation rank. -/
theorem step_match (canonical : Canonical p q) (typed : State.Typed p source ty)
    (related : Related p source target) (step : Step p responses source next) :
    Matched p q responses source target next := by
  cases related with
  | eval code lowered sites placed => exact eval_step canonical.1 typed step lowered code placed sites
  | ret code placed atResult => exact return_step canonical.1 typed step code placed atResult
  | lengthReady code initialLowered yesLowered noLowered le fresh initialSites yesSites noSites placed =>
      exact lengthReady_step canonical.1 typed step initialLowered yesLowered noLowered code placed le
        fresh initialSites yesSites noSites
  | allocate code yesLowered noLowered le fresh yesSites noSites placed =>
      exact allocate_step (program_metadata canonical.2).2.2.1 step yesLowered noLowered code placed le fresh yesSites noSites
  | readCheck code placed => exact readCheck_step canonical.1 typed step code placed
  | readCell code placed => exact readCell_step canonical.1 typed step code placed
  | writeCheck code lowered le sites placed => exact writeCheck_step canonical.1 typed step lowered code placed le sites
  | store code placed => exact store_step canonical.1 typed step code placed
  | invoke code placed => exact invoke_step canonical code placed typed step
  | grant code placed => exact grant_step canonical code placed typed step
  | close code placed =>
      cases code with
      | owner parent => exact close_step canonical.1 typed step parent placed
  | revoke code placed => exact revoke_step code placed step
  | restore code placed => exact restore_step code placed step
  | trap => cases step

/-- Completed source executions have finite target executions with the same outcome and World. -/
theorem core_to_mir (canonical : Canonical p q) (typed : State.Typed p source ty)
    (related : Related p source target) (path : Steps p responses source last) (done : Terminal last) :
    ∃ targetLast, Mir.Steps q responses target targetLast ∧ Mir.Terminal targetLast ∧ FinalRelated p last targetLast := by
  apply finite_forward canonical.1 (Related p) (FinalRelated p) ?_ ?_ typed related path done
  · intro source target next hs hr step
    obtain ⟨count, targetNext, segment, following, _⟩ := step_match canonical hs hr step
    exact ⟨count, targetNext, segment, following⟩
  · intro source target _ hr terminal
    exact terminal_flush hr terminal

/-- Finite raw-stopped target executions reflect to completed core executions.
The proof consumes actual target steps, with strict coreRank descent for each zero-step match. -/
theorem mir_to_core (canonical : Canonical p q) (typed : State.Typed p source ty)
    (related : Related p source target) (path : Mir.Steps q responses target last) (done : Mir.RawStopped last) :
    ∃ sourceLast, Steps p responses source sourceLast ∧ Terminal sourceLast ∧ FinalRelated p sourceLast last := by
  exact finite_reflection canonical.1 (Related p) coreRank (FinalRelated p)
    (fun hs hr step => step_match canonical hs hr step)
    (fun _ hr terminal => terminal_flush hr terminal) typed related path done

/-- Invalid is excluded for every finite target prefix from a related checked core state. -/
theorem mir_prefix_not_invalid (canonical : Canonical p q) (typed : State.Typed p source ty)
    (related : Related p source target) (path : Mir.Steps q responses target last) :
    last.control ≠ .invalid := by
  intro invalid
  have stopped : Mir.RawStopped last := by simp [Mir.RawStopped, invalid]
  obtain ⟨_, _, _, final⟩ := mir_to_core canonical typed related path stopped
  exact final.1.target_not_invalid invalid

/-- Entry specialization has no assumed initial relation or target-validity premise. -/
theorem core_entry_to_mir (canonical : Canonical p q)
    (path : Steps p responses (ANL.Words.initial p) last) (done : Terminal last) :
    ∃ targetLast, Mir.Steps q responses (Mir.initial q) targetLast ∧ Mir.Terminal targetLast ∧
      FinalRelated p last targetLast :=
  core_to_mir canonical (entry_typed canonical.1) (initial_related canonical) path done

theorem mir_entry_to_core (canonical : Canonical p q)
    (path : Mir.Steps q responses (Mir.initial q) last) (done : Mir.RawStopped last) :
    ∃ sourceLast, Steps p responses (ANL.Words.initial p) sourceLast ∧ Terminal sourceLast ∧
      FinalRelated p sourceLast last :=
  mir_to_core canonical (entry_typed canonical.1) (initial_related canonical) path done

theorem mir_entry_not_invalid (canonical : Canonical p q)
    (path : Mir.Steps q responses (Mir.initial q) last) : last.control ≠ .invalid :=
  mir_prefix_not_invalid canonical (entry_typed canonical.1) (initial_related canonical) path

/-- Both machines suspend execution access to callee descriptors during restore. -/
theorem Related.accessible (related : Related p source target) :
    target.accessible.map Prod.snd = source.accessible.map binding := by
  obtain ⟨_, _, runtime⟩ := related.runtime
  have values := runtime.current.resources.values
  cases related with
  | ret _ _ resultAt => cases resultAt <;> exact values
  | restore => rfl
  | _ => exact values

theorem FinalRelated.world (related : FinalRelated p source target) : source.world = target.world :=
  related.1.world

theorem FinalRelated.runtime (related : FinalRelated p source target) :
    ∃ locals ids, RuntimeRel locals ids source target := related.1.runtime

/-- Completed runner correspondence uses independently chosen budgets. -/
theorem core_completed_run_to_mir (canonical : Canonical p q)
    (completed : ANL.Words.execute p responses coreBudget (ANL.Words.initial p) = .completed sourceLast) :
    ∃ mirBudget targetLast, Mir.run q responses mirBudget (Mir.initial q) = .completed targetLast ∧
      FinalRelated p sourceLast targetLast := by
  have sourcePath := (execute_completed_sound completed).1
  have sourceDone := (execute_completed_safe canonical.1 (entry_typed canonical.1) completed).2
  obtain ⟨targetLast, targetPath, targetDone, related⟩ := core_entry_to_mir canonical sourcePath sourceDone
  obtain ⟨mirBudget, targetRun⟩ := Mir.run_complete targetPath targetDone.rawStopped
  exact ⟨mirBudget, targetLast, targetRun, related⟩

theorem mir_completed_run_to_core (canonical : Canonical p q)
    (completed : Mir.run q responses mirBudget (Mir.initial q) = .completed targetLast) :
    ∃ coreBudget sourceLast, ANL.Words.execute p responses coreBudget (ANL.Words.initial p) = .completed sourceLast ∧
      FinalRelated p sourceLast targetLast := by
  obtain ⟨targetPath, targetDone⟩ := Mir.run_completed_sound completed
  obtain ⟨sourceLast, sourcePath, sourceDone, related⟩ := mir_entry_to_core canonical targetPath targetDone
  obtain ⟨coreBudget, sourceRun⟩ := execute_completed_complete sourcePath (Or.inl sourceDone)
  exact ⟨coreBudget, sourceLast, sourceRun, related⟩

theorem mir_completed_terminal (canonical : Canonical p q)
    (completed : Mir.run q responses mirBudget (Mir.initial q) = .completed targetLast) : Mir.Terminal targetLast := by
  obtain ⟨targetPath, targetDone⟩ := Mir.run_completed_sound completed
  obtain ⟨_, _, _, related⟩ := mir_entry_to_core canonical targetPath targetDone
  exact related.2.1

theorem mir_run_not_invalid (canonical : Canonical p q) :
    (Mir.run q responses budget (Mir.initial q)).state.control ≠ .invalid :=
  mir_entry_not_invalid canonical (Mir.run_spec q responses budget (Mir.initial q)).1

/-- Normal target completion releases all owned storage and leaves no accessible resource binding. -/
theorem mir_normal_entry_cleanup (canonical : Canonical p q)
    (path : Mir.Steps q responses (Mir.initial q) ⟨.ret value, targetActivation, [], world⟩) :
    value.type = .scalar (.legacy .i64) ∧ world.owners = [] ∧ targetActivation.resources = [] ∧
      world.positiveHeap = [] ∧ world.activeEmpties = [] := by
  obtain ⟨sourceLast, sourcePath, _, related⟩ := mir_entry_to_core canonical path rfl
  rcases sourceLast with ⟨sourceControl, sourceActivation, sourceKont, sourceWorld⟩
  rcases related.2.2 with normal | trapped
  · obtain ⟨result, sourceResult, sourceStack, targetResult, _⟩ := normal
    simp only [Mir.Control.ret.injEq] at targetResult
    cases targetResult
    change sourceControl = .ret value at sourceResult
    change sourceKont = [] at sourceStack
    subst sourceControl
    subst sourceKont
    have worldEq : sourceWorld = world := related.world
    subst sourceWorld
    obtain ⟨typedValue, owners, resources, positive, empty⟩ := normal_entry_cleanup canonical.1 sourcePath
    obtain ⟨_, _, runtime⟩ := related.runtime
    have targetResources : targetActivation.resources = [] := by
      apply (List.map_eq_nil_iff (f := Prod.snd)).mp
      simpa only [resources, List.map_nil] using runtime.current.resources.values
    exact ⟨typedValue, owners, targetResources, positive, empty⟩
  · obtain ⟨_, _, impossible⟩ := trapped
    cases impossible

end ANL.Words.Simulation
