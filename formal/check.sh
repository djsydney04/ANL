#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
printf '%s\n' 'Checking proof sources for prohibited declarations'
python3 - <<'PY'
import re
from pathlib import Path
for path in [Path('Main.lean'), Path('APL.lean'), *Path('APL').glob('*.lean')]:
    if re.search(r'\b(sorry|admit)\b|^\s*(?:(?:private|protected)\s+)?(?:axiom|unsafe)\b', path.read_text(), re.M):
        raise SystemExit(f'prohibited proof bypass or unsafe declaration in {path}')
PY
printf '%s\n' 'Building proofs and formal evaluator from clean artifacts'
lake clean
lake build
printf '%s\n' 'Auditing theorem axiom dependencies'
lake env lean -DwarningAsError=true APL/Audit.lean
printf '%s\n' 'Replaying declarations through the Lean kernel'
lake env leanchecker --verbose APL.Core APL.Machine APL.Semantics APL.Smoke APL.ProgramSemantics
printf '%s\n' 'Proof checks completed successfully'
