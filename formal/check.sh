#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
printf '%s\n' 'Checking proof sources for prohibited declarations'
python3 - <<'PY'
import re
from pathlib import Path
for path in [*Path('.').glob('*.lean'), *Path('APL').rglob('*.lean'), *Path('ANL').rglob('*.lean')]:
    text = path.read_text()
    if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(?:(?:private|protected)\s+)?(?:axiom|unsafe)\b', text, re.M):
        raise SystemExit(f'prohibited proof bypass or unsafe declaration in {path}')
    if path.parts[0] == 'ANL' and re.search(r'^\s*(?:(?:private|protected)\s+)?partial\s+def\b', text, re.M):
        raise SystemExit(f'partial ANL declaration in {path}')
anl = {str(p.with_suffix('')).replace('/', '.') for p in Path('ANL').rglob('*.lean') if p != Path('ANL/Audit.lean')}
modules = [line.strip() for line in Path('anl-kernel-modules.txt').read_text().splitlines() if line.strip() and not line.startswith('#')]
expected = anl | {'MemoryPairMain', 'MemoryRawProbe', 'MemoryReferenceMain', 'WordsPairMain', 'WordsRawProbe', 'WordsReferenceMain', 'BootRawProbe'}
if len(modules) != len(set(modules)) or set(modules) != expected:
    raise SystemExit('ANL kernel inventory must cover every model and command module exactly once')
umbrella_text = Path('ANL.lean').read_text()
umbrella = re.findall(r'^import (ANL\.[A-Za-z0-9_.]+)$', umbrella_text, re.M)
if len(umbrella) != len(set(umbrella)) or set(umbrella) != anl:
    raise SystemExit('ANL umbrella must import every model module exactly once')
if re.sub(r'^import ANL\.[A-Za-z0-9_.]+$', '', umbrella_text, flags=re.M).strip():
    raise SystemExit('ANL umbrella must contain imports only; replay declarations in explicit modules')
audit = re.search(r'let modules := #\[(.*?)\]', Path('ANL/Audit.lean').read_text(), re.S)
audited = re.findall(r'`(ANL\.[A-Za-z0-9_.]+)', audit.group(1)) if audit else []
if len(audited) != len(set(audited)) or set(audited) != anl:
    raise SystemExit('ANL declaration audit must cover every model module exactly once')
PY
printf '%s\n' 'Building proofs and formal evaluator from clean artifacts'
lake clean
lake build
printf '%s\n' 'Auditing theorem axiom dependencies'
lake env lean -DwarningAsError=true APL/Audit.lean
lake env lean -DwarningAsError=true ANL/Audit.lean
# Separate processes avoid Lean 4.36.0's freed-import cache bug (leanprover/lean4#16267).
for module in APL.Core APL.Machine APL.Semantics APL.Smoke APL.Program APL.ProgramSemantics APL.ProgramTyping APL.ProgramSafety APL.ProgramEvalSoundness APL.ProgramEvalCompleteness APL.VCG APL.VCGContracts APL.VCGCalls APL.VCGCallsExamples APL.LocalState APL.LocalStateTyping APL.LocalStateRun APL.LocalStateSafety APL.LocalStateEmbedding APL.LocalStateExamples APL.StateVCG APL.StateVCGContracts APL.StateVCGExamples APL.LocalStateFrame APL.LoopVCGSupport APL.LoopAnnotations APL.LocalStateContinuation APL.LoopVCG APL.LoopVCGBounds APL.LoopVCGSoundness APL.LoopVCGContracts APL.LoopVCGQueries APL.LoopVCGExamples APL.LoopGenerationSupport APL.LoopGenerationRank APL.LoopGenerationComplete APL.LoopGenerationCorollaries APL.LoopGenerationExamples APL.FlatProductsValues APL.FlatProductsMachine APL.FlatProductsTyping APL.FlatProductsRun APL.FlatProductsSafety APL.FlatProductsEmbedding APL.FlatProductsExamples APL.Wire APL.FlatProductsWire APL.FlatProductsWireSafety APL.FlatProductsFrame APL.FlatProductsContinuation APL.ProductLogicScalar APL.ProductLogicValues APL.ProductLogicLayout APL.ProductAnnotations APL.ProductFlowSupport APL.ProductSpec APL.ProductEntry APL.ProductClauses APL.ProductSupport APL.ProductRuntime APL.ProductFlow APL.ProductFlowBounds APL.ProductFlowSemantics APL.ProductFlowLoops APL.ProductFlowRules APL.ProductFlowBoolean APL.ProductFlowCalls APL.ProductFlowSoundness APL.ProductContractClauses APL.ProductQueries APL.ProductContracts APL.ProductContractQueries; do
    printf 'Replaying %s through the Lean kernel\n' "$module"
    lake env leanchecker --verbose "$module"
done
# leanchecker treats ANL as a prefix, expanding it to concurrent module replays.
# The import-only umbrella is covered by the inventory check above.
while IFS= read -r module; do
    case "$module" in ''|\#*) continue ;; esac
    printf 'Replaying %s through the Lean kernel\n' "$module"
    lake env leanchecker --verbose "$module"
done < anl-kernel-modules.txt
printf '%s\n' 'Proof checks completed successfully'
