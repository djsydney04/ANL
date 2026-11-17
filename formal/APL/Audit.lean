import APL.ProgramSafety
import Lean

open Lean Elab Command in
run_elab do
  let names := #[``APL.infer_complete, ``APL.infer_sound, ``APL.type_unique,
    ``APL.checked_typed, ``APL.division_typed, ``APL.unary_typed, ``APL.binary_typed,
    ``APL.lookup_typed, ``APL.resume_typed, ``APL.shortCircuit_typed,
    ``APL.step_preserves, ``APL.progress, ``APL.step_complete, ``APL.step_sound,
    ``APL.preservation, ``APL.relational_progress, ``APL.run_sound, ``APL.run_complete,
    ``APL.steps_preserve, ``APL.run_safety, ``APL.closed_safety,
    ``APL.Program.infer_complete, ``APL.Program.infer_sound, ``APL.Program.type_unique,
    ``APL.Program.signatures_lookup, ``APL.Program.signatures_lookup_inv, ``APL.Program.checked_functions,
    ``APL.Program.resume_typed, ``APL.Program.preservation, ``APL.Program.progress,
    ``APL.Program.steps_preserve, ``APL.Program.safety, ``APL.Program.no_invalid,
    ``APL.Program.closed_safety, ``APL.Program.entry_typed, ``APL.Program.entry_safety]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on prohibited axiom {axiomName}"
    logInfo m!"{name}: {axioms}"
