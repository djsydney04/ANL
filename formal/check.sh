#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
python3 - <<'PY'
import re
from pathlib import Path
for path in [Path('Main.lean'), Path('APL.lean'), *Path('APL').glob('*.lean')]:
    if re.search(r'\b(sorry|admit)\b|^\s*(?:(?:private|protected)\s+)?(?:axiom|unsafe)\b', path.read_text(), re.M):
        raise SystemExit(f'prohibited proof bypass or unsafe declaration in {path}')
PY
lake clean
lake build
lake env lean -DwarningAsError=true APL/Audit.lean
lake env leanchecker APL.Core APL.Machine APL.Semantics APL.Smoke APL.ProgramSemantics
