#!/usr/bin/env python3
"""Capture actual C inputs, then pass arguments unchanged to an explicit compiler."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time


def save(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")


def main():
    scratch = Path(os.environ["ANL_CORPUS_SCRATCH"]).resolve(strict=True)
    logs = Path(os.environ["ANL_CORPUS_CC_LOG"])
    real = Path(os.environ["ANL_CORPUS_REAL_CC"]).resolve(strict=True)
    expected = os.environ["ANL_CORPUS_REAL_CC_SHA256"]
    if not logs.is_absolute() or scratch not in logs.resolve().parents:
        raise RuntimeError("capture directory is outside the capture run root")
    if hashlib.sha256(real.read_bytes()).hexdigest() != expected:
        raise RuntimeError("real compiler identity changed")
    logs.mkdir(parents=True, exist_ok=True)
    here = Path(tempfile.mkdtemp(prefix="call-", dir=logs))
    argv = sys.argv[1:]
    candidates = set()
    for word in argv:
        path = Path(word)
        if path.is_file() and path.suffix in (".c", ".h", ".o"):
            candidates.add(path.resolve())
            if path.suffix == ".c":
                candidates.update(p.resolve() for p in path.parent.glob("*.h") if p.is_file())
    records = []
    total = 0
    for index, path in enumerate(sorted(candidates, key=os.fsencode)):
        with path.open("rb") as source:
            data = source.read(67_108_865)
        total += len(data)
        if len(data) > 67_108_864 or total > 134_217_728:
            raise RuntimeError("C capture bound exceeded")
        name = f"input-{index:03d}{path.suffix}"
        (here / name).write_bytes(data)
        records.append(dict(path=os.fsdecode(path), path_bytes_hex=os.fsencode(path).hex(),
                            file=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
    record = dict(argv=[str(real), *argv], real_cc_sha256=expected, inputs=records,
                  changed_arguments=False, exit=None)
    save(here / "command.json", record)
    result = subprocess.run([str(real), *argv], check=False)
    record["exit"] = result.returncode
    save(here / "command.json", record)
    return result.returncode if result.returncode >= 0 else 128 - result.returncode


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as error:
        print("corpus compiler adapter: " + str(error), file=sys.stderr)
        sys.exit(98)
