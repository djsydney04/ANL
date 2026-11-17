import ANL
import Lean

set_option pp.explicit true
set_option maxHeartbeats 4000000

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let modules := #[
    `ANL.MemoryCore,
    `ANL.MemoryTyping,
    `ANL.MemoryHeap,
    `ANL.MemoryMachine,
    `ANL.MemoryRun,
    `ANL.MemoryInvariant,
    `ANL.MemoryLayout,
    `ANL.MemorySafety,
    `ANL.MemoryExecute,
    `ANL.MemoryEmbedding,
    `ANL.MemoryEmbeddingTyping,
    `ANL.MemoryEmbeddingExecution,
    `ANL.MemoryLoans,
    `ANL.MemoryMir,
    `ANL.MemoryMirTyping,
    `ANL.MemoryLowering,
    `ANL.MemoryLoweringInventory,
    `ANL.MemoryLoweringSupport,
    `ANL.MemoryLoweringTyping,
    `ANL.MemoryLoweringProofs,
    `ANL.MemoryMirMachine,
    `ANL.MemoryMirRun,
    `ANL.MemoryMirRunProofs,
    `ANL.MemorySimulationData,
    `ANL.MemorySimulationValues,
    `ANL.MemorySimulationAdmin,
    `ANL.MemorySimulationRank,
    `ANL.MemorySimulationContinuation,
    `ANL.MemorySimulationKontInvariant,
    `ANL.MemorySimulationBounds,
    `ANL.MemorySimulationStore,
    `ANL.MemorySimulationTemps,
    `ANL.MemorySimulationFinite,
    `ANL.MemorySimulationRelation,
    `ANL.MemorySimulationInitial,
    `ANL.MemorySimulationReturn,
    `ANL.MemorySimulationLimits,
    `ANL.MemorySimulationPlacement,
    `ANL.MemorySimulationMatch,
    `ANL.MemorySimulationContext,
    `ANL.MemorySimulationSites,
    `ANL.MemorySimulationEval,
    `ANL.MemorySimulationReturnBindings,
    `ANL.MemorySimulationReturnScalar,
    `ANL.MemorySimulationReturnControl,
    `ANL.MemorySimulationReturnArguments,
    `ANL.MemorySimulationResources,
    `ANL.MemorySimulationMemoryPhases,
    `ANL.MemorySimulationReturnMemory,
    `ANL.MemorySimulationRetTyping,
    `ANL.MemorySimulationReturnStep,
    `ANL.MemorySimulationClose,
    `ANL.MemorySimulationCallBindings,
    `ANL.MemorySimulationCallPhases,
    `ANL.MemoryLoweringSoundness,
    `ANL.MemoryOrigin,
    `ANL.MemoryPair,
    `ANL.MemoryWire,
    `ANL.MemoryWireSafety,
    `ANL.MemoryPairSemantics,
    `ANL.MemoryResources,
    `ANL.MemoryResourceRun,
    `ANL.MemoryResourcePolicy,
    `ANL.MemoryResourceAccounting,
    `ANL.MemoryResourceDepth,
    `ANL.MemoryResourceEntry,
    `ANL.MemoryReference,
    `ANL.MemoryReferenceBounds,
    `ANL.MemoryWireIO,
    `ANL.MemoryReferenceOutput,
    `ANL.MemoryReferenceIO,
    `ANL.MemoryReferenceSafety]
  let allowedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
  let expectedShims := #[
    `ANL.Memory.ViewMode.ctorIdx._impl,
    `ANL.Memory.Mode.ctorIdx._impl,
    `ANL.Memory.Term.ctorIdx._impl,
    `ANL.Memory.Ref.ctorIdx._impl,
    `ANL.Memory.Response.ctorIdx._impl,
    `ANL.Memory.Allocation.ctorIdx._impl,
    `ANL.Memory.Event.ctorIdx._impl,
    `ANL.Memory.Owner.ctorIdx._impl,
    `ANL.Memory.MemoryTrap.ctorIdx._impl,
    `ANL.Memory.Frame.ctorIdx._impl,
    `ANL.Memory.Control.ctorIdx._impl,
    `ANL.Memory.RunResult.ctorIdx._impl,
    `ANL.Memory.Mir.Block.ctorIdx._impl,
    `ANL.Memory.Mir.Operation.ctorIdx._impl,
    `ANL.Memory.Mir.Trap.ctorIdx._impl,
    `ANL.Memory.Mir.Frame.ctorIdx._impl,
    `ANL.Memory.Mir.Control.ctorIdx._impl,
    `ANL.Memory.Mir.RunResult.ctorIdx._impl,
    `ANL.Memory.Lowering.Local.ctorIdx._impl,
    `ANL.Memory.Lowering.InventoryProof.Kind.ctorIdx._impl,
    `ANL.Memory.Tool.Limit.ctorIdx._impl,
    `ANL.Memory.Tool.Preflight.ctorIdx._impl,
    `ANL.Memory.Tool.Tick.ctorIdx._impl,
    `ANL.Memory.Tool.Result.ctorIdx._impl,
    `ANL.Memory.Simulation.ResultTarget.ctorIdx._impl,
    `ANL.Memory.Simulation.Capture.ctorIdx._impl,
    `ANL.Memory.Simulation.KontCode.ctorIdx._impl,
    `ANL.Memory.Wire.ErrorKind.ctorIdx._impl,
    `ANL.Memory.Wire.IOBoundary.Status.ctorIdx._impl,
    `ANL.Memory.Reference.RunError.ctorIdx._impl,
    `ANL.Memory.Reference.Status.ctorIdx._impl,
    `ANL.Memory.Reference.Completion.ctorIdx._impl,
    `ANL.Memory.Reference.ExportError.ctorIdx._impl]
  let mut inspected : Array Name := #[]
  let mut total : Nat := 0
  for moduleName in modules do
    let some moduleIdx := env.getModuleIdx? moduleName | throwError "Missing module {moduleName}"
    let mut count : Nat := 0
    for (name, info) in env.constants.toList do
      if env.getModuleIdxFor? name == some moduleIdx then
        match info with
        | .axiomInfo _ => throwError "Source axiom {name}"
        | _ => pure ()
        if info.isUnsafe then
          unless expectedShims.contains name do throwError "Unexpected unsafe declaration {name}"
          let some value := info.value? | throwError "Missing generated body {name}"
          unless value.getNumHeadLambdas > 0 do throwError "Non-wrapper generated body {name}"
          let .app (.app (.const tag _) _) (.bvar 0) := value.getLambdaBody
            | throwError "Unexpected generated body {name}: {value}"
          unless tag == ``getObjTagNat do throwError "Unexpected generated primitive {name}: {tag}"
          inspected := inspected.push name
          logInfo m!"INSPECTED_UNSAFE {name}\nTYPE {info.type}\nBODY {value}"
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless allowedAxioms.contains axiomName do
            throwError "Prohibited axiom {axiomName} in {name}"
        logInfo m!"AUDITED {moduleName} {name}: {axioms}"
        count := count + 1
    unless count > 0 do throwError "Empty declaration audit for {moduleName}"
    total := total + count
    logInfo m!"MODULE {moduleName} declarations={count}"
  for name in expectedShims do
    unless inspected.contains name do throwError "Expected generated wrapper was not inspected: {name}"
  logInfo m!"TOTAL declarations={total} inspectedGeneratedWrappers={inspected.size}"
