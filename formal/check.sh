#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
printf '%s\n' 'Checking proof sources for prohibited declarations'
python3 - <<'PY'
import re
from pathlib import Path
for path in [*Path('.').glob('*.lean'), *Path('APL').glob('*.lean')]:
    if re.search(r'\b(sorry|admit)\b|^\s*(?:(?:private|protected)\s+)?(?:axiom|unsafe)\b', path.read_text(), re.M):
        raise SystemExit(f'prohibited proof bypass or unsafe declaration in {path}')
PY
printf '%s\n' 'Building proofs and formal evaluator from clean artifacts'
lake clean
lake build
printf '%s\n' 'Auditing theorem axiom dependencies'
lake env lean -DwarningAsError=true APL/Audit.lean
# Separate processes avoid Lean 4.36.0's freed-import cache bug (leanprover/lean4#16267).
for module in APL.Core APL.Machine APL.Semantics APL.Smoke APL.Program APL.ProgramSemantics APL.ProgramTyping APL.ProgramSafety APL.ProgramEvalSoundness APL.ProgramEvalCompleteness APL.VCG APL.VCGContracts APL.VCGCalls APL.VCGCallsExamples APL.LocalState APL.LocalStateTyping APL.LocalStateRun APL.LocalStateSafety APL.LocalStateEmbedding APL.LocalStateExamples APL.StateVCG APL.StateVCGContracts APL.StateVCGExamples APL.LocalStateFrame APL.LoopVCGSupport APL.LoopAnnotations APL.LocalStateContinuation APL.LoopVCG APL.LoopVCGBounds APL.LoopVCGSoundness APL.LoopVCGContracts APL.LoopVCGQueries APL.LoopVCGExamples APL.LoopGenerationSupport APL.LoopGenerationRank APL.LoopGenerationComplete APL.LoopGenerationCorollaries APL.LoopGenerationExamples APL.FlatProductsValues APL.FlatProductsMachine APL.FlatProductsTyping APL.FlatProductsRun APL.FlatProductsSafety APL.FlatProductsEmbedding APL.FlatProductsExamples; do
    printf 'Replaying %s through the Lean kernel\n' "$module"
    lake env leanchecker --verbose "$module"
done
printf '%s\n' 'Proof checks completed successfully'
