#!/usr/bin/env python3
"""Record forbidden compiler/solver startup in a capture sentinel."""
import json
import os
from pathlib import Path
import sys

path = Path(os.environ["ANL_CORPUS_SPY_LOG"])
with path.open("ab") as target:
    target.write((json.dumps({"argv": sys.argv}) + "\n").encode())
sys.exit(99)
