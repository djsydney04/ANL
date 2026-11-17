import APL.VCGCallsExamples
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
    ``APL.Program.closed_safety, ``APL.Program.entry_typed, ``APL.Program.entry_safety,
    ``APL.Program.eval_value_sound, ``APL.Program.eval_trap_sound, ``APL.Program.eval_invalid_sound,
    ``APL.Program.eval_value_typed, ``APL.Program.eval_ne_invalid,
    ``APL.Program.eval_value_complete, ``APL.Program.eval_trap_complete, ``APL.Program.eval_invalid_complete,
    ``APL.VCG.EnvRep.lookup, ``APL.VCG.wp_eval_sound, ``APL.VCG.wp_value, ``APL.VCG.wp_no_trap,
    ``APL.VCG.wp_no_invalid, ``APL.VCG.wp_steps_value, ``APL.VCG.wp_steps_no_trap, ``APL.VCG.wp_steps_no_invalid,
    ``APL.VCG.instantiate_sound, ``APL.VCG.spec_post_sound, ``APL.VCG.requires_vc_sound,
    ``APL.VCG.contract_eval_sound, ``APL.VCG.contract_preconditions_defined, ``APL.VCG.contract_nonvacuous,
    ``APL.VCG.contract_steps_value, ``APL.VCG.contract_steps_no_trap, ``APL.VCG.contract_steps_no_invalid,
    ``APL.VCG.short_guard,
    ``APL.VCG.not_shortable,
    ``APL.VCG.unary_wp_sound,
    ``APL.VCG.binary_wp_sound,
    ``APL.VCG.env_reverse,
    ``APL.VCG.typed_parameters_rep,
    ``APL.VCG.invokeWP_preconditions,
    ``APL.VCG.wpCalls_eval_sound,
    ``APL.VCG.wpCalls_value,
    ``APL.VCG.wpCalls_no_trap,
    ``APL.VCG.wpCalls_no_invalid,
    ``APL.VCG.wpCalls_steps_value,
    ``APL.VCG.wpCalls_steps_no_trap,
    ``APL.VCG.wpCalls_steps_no_invalid,
    ``APL.VCG.calls_contract_eval_sound,
    ``APL.VCG.calls_contract_preconditions_defined,
    ``APL.VCG.calls_contract_nonvacuous,
    ``APL.VCG.calls_contract_steps_value,
    ``APL.VCG.calls_contract_steps_no_trap,
    ``APL.VCG.calls_contract_steps_no_invalid]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on prohibited axiom {axiomName}"
    logInfo m!"{name}: {axioms}"
