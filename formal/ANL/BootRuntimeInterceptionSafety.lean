import ANL.BootRuntimeOccurrenceTyping

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program} {s : State} {ident : Nat}
set_option linter.unusedSimpArgs false

 theorem typed_invoke_arguments_at {machine : Words.State} (typed : Words.State.Typed p.carrier machine t)
    (controlEq : machine.control = .invoke ident none values)
    (found : p.functions[ident]? = some (.primitive row)) : values.reverse.map Val.type = row.params := by
  cases machine with | mk ctl a k w =>
   simp only at controlEq
   subst ctl
   exact typed_invoke_arguments typed found

 theorem capture_complete (wf : WellFormedProgram p) (typed : Words.State.Typed p.carrier s.machine t)
    (aligned : Origin.Aligned p s.machine s.origins) (frontier : Origin.PrimitiveFrontier p s.machine)
    (ordinal : 0 < s.nextOrdinal) : ∃ q, Captured p s q := by
  obtain ⟨ident, values, row, ty, args, controlEq, found, located, arity⟩ := Origin.primitive_capture aligned frontier
  have policy := primitive_valid wf found
  have params := (typed_invoke_arguments_at typed controlEq found).trans policy.params
  have result := located_call_result wf located found
  refine ⟨_, Captured.invoke controlEq found ?_⟩
  refine ⟨rfl, aligned.function, ordinal, policy.operation, params, ?_⟩
  simp only [controlEq, found, Origin.lookup_iff.mpr located]
  exact ⟨True.intro, True.intro, True.intro, result, by simpa using arity.symm, True.intro⟩

 theorem capture_some (wf : WellFormedProgram p) (typed : Words.State.Typed p.carrier s.machine t)
    (aligned : Origin.Aligned p s.machine s.origins) (frontier : Origin.PrimitiveFrontier p s.machine)
    (ordinal : 0 < s.nextOrdinal) : ∃ q, capture p s = some q := by
  obtain ⟨q, captured⟩ := capture_complete wf typed aligned frontier ordinal
  exact ⟨q, capture_iff.mpr captured⟩

 theorem PendingAt.invocation (valid : PendingAt p s q) :
    ∃ values row, s.machine.control = .invoke q.declaration none values ∧
      p.functions[q.declaration]? = some (.primitive row) ∧ row.operation = q.operation ∧ values.reverse = q.arguments := by
  rcases valid with ⟨_, _, _, _, _, facts⟩
  split at facts
  next ident values row ty target terms controlEq found located =>
    rcases facts with ⟨rfl, _, operation, _, _, arguments⟩
    exact ⟨values, row, controlEq, found, operation, arguments⟩
  next => contradiction

 theorem return_typed (wf : WellFormedProgram p) (typed : Words.State.Typed p.carrier s.machine t)
    (pending : PendingAt p s q) (result : value.type = q.operation.result) :
    Words.State.Typed p.carrier (returnState s value).machine t := by
  obtain ⟨values, row, controlEq, found, operation, _⟩ := pending.invocation
  have result' : value.type = row.result := by rw [(primitive_valid wf found).result, operation]; exact result
  cases s with | mk machine origins phase hardware episode stack cursor ordinal events used seen parked snapshot =>
   cases machine with | mk ctl a k w =>
    simp only at controlEq
    subst ctl
    exact invoke_return_typed typed found result'

 theorem return_aligned (aligned : Origin.Aligned p s.machine s.origins) :
    Origin.Aligned p (returnState s value).machine (returnState s value).origins := by
  obtain ⟨term, located⟩ := aligned.control.located
  exact ⟨aligned.function, .ret located, aligned.frames⟩

 theorem return_memory (memory : MemoryFreeState s.machine) : MemoryFreeState (returnState s value).machine := memory
 theorem return_episode (episode : EpisodeChain s.machine.current.function s.machine.kont role) :
    EpisodeChain (returnState s value).machine.current.function (returnState s value).machine.kont role := episode

 theorem with_phase_invariant (old : RuntimeInvariant p env s) (phase : PhaseInvariant p (withPhase s nextPhase)) :
    RuntimeInvariant p env (withPhase s nextPhase) :=
  ⟨old.typed, old.aligned, old.memory, old.hardware, old.installed, old.stack, old.episode,
    phase, old.cursor, old.ordinal, old.bootSeen, old.passive⟩

 theorem captured_invariant (old : RuntimeInvariant p env s) (captured : Captured p s q) :
    RuntimeInvariant p env (withPhase s (.primitiveBefore q)) :=
  with_phase_invariant old (.before rfl ⟨captured.valid, captured.ordinal⟩)

 theorem return_invariant (wf : WellFormedProgram p) (old : RuntimeInvariant p env s)
    (valid : AfterValid p s q value) : RuntimeInvariant p env (returnState s value) :=
  ⟨return_typed wf old.typed valid.1 valid.2.2, return_aligned old.aligned, old.memory,
    old.hardware, old.installed, old.stack, old.episode, .ordinary rfl,
    old.cursor, old.ordinal, old.bootSeen, old.passive⟩

 theorem effect_payload (effect : OperationEffect env h cursor op args result)
    (operation : q.operation = op) (arguments : q.arguments = args) : PayloadValue q result.payload result.value := by
  cases effect with
  | read _ value => exact .read operation value
  | write value => exact .write operation arguments value
  | fence => exact .fence operation
  | clear => exact .clear operation
  | set => exact .set operation
  | install => exact .install operation

 theorem effect_installed (effect : Effect p env h cursor op args result)
    (installed : h.installedHandler = none ∨ h.installedHandler = some p.entries.hardware.function) :
    result.hardware.installedHandler = none ∨ result.hardware.installedHandler = some p.entries.hardware.function := by
  have policy := effect.operation
  cases effect.effect
  all_goals first | exact installed | (cases policy; exact .inr rfl)

 theorem effect_cursor_bound (effect : Effect p env h cursor op args result) (bound : cursor ≤ env.reads.length) :
    result.cursor ≤ env.reads.length := by
  rcases effect.cursor_change with ⟨n, _, increment, found⟩ | same
  · have within := (List.getElem?_eq_some_iff.mp found).1
    omega
  · omega

 theorem commit_invariant (old : RuntimeInvariant p env s) (valid : BeforeValid p s q)
    (effect : Effect p env s.hardware s.readCursor q.operation q.arguments result) :
    RuntimeInvariant p env (commitState s q result) := by
  refine ⟨old.typed, old.aligned, old.memory, effect.hardware_valid, effect_installed effect old.installed,
    old.stack, old.episode, ?_, effect_cursor_bound effect old.cursor, Nat.zero_lt_succ _, old.bootSeen, old.passive⟩
  apply PhaseInvariant.after rfl
  · exact ⟨valid.1, congrArg (· + 1) valid.2, effect.effect.result_type⟩
  · exact ⟨result.payload, s.revEvents, rfl, effect_payload effect.effect rfl rfl⟩

end ANL.Boot.Runtime
