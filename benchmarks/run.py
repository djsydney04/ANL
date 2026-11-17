#!/usr/bin/env python3
"""Measure checked CLI invocations against explicit, versioned semantic oracles."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


class SemanticFailure(RuntimeError):
    pass


def validate(result: dict, expected: dict, context: str) -> None:
    """Fail closed on wrong values, traps, statuses, or missing diagnostics."""
    if result["exit"] != expected["exit"]:
        raise SemanticFailure(f"{context}: wrong exit; expected {expected}, observed {result}")
    if "stdout" in expected and result["stdout"] != expected["stdout"]:
        raise SemanticFailure(f"{context}: wrong stdout; expected {expected}, observed {result}")
    if expected["exit"] == 0 and result["stderr"]:
        raise SemanticFailure(f"{context}: successful command wrote stderr: {result}")
    if expected["exit"] != 0 and not result["stderr"]:
        raise SemanticFailure(f"{context}: failure lacked a diagnostic: {result}")
    if expected.get("stderr_contains", "") not in result["stderr"]:
        raise SemanticFailure(f"{context}: wrong diagnostic; expected {expected}, observed {result}")


def invoke(command: list[str], timeout: float) -> dict:
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.perf_counter_ns()
    try:
        process = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired as error:
        raise SemanticFailure(f"command exceeded {timeout}s: {command}") from error
    elapsed = time.perf_counter_ns() - started
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    return {
        "exit": process.returncode,
        "stdout": process.stdout,
        "stderr": process.stderr,
        "elapsed_ms": elapsed / 1_000_000,
        "user_cpu_ms": (after.ru_utime - before.ru_utime) * 1000,
        "system_cpu_ms": (after.ru_stime - before.ru_stime) * 1000,
    }


def capture(command: list[str]) -> str:
    process = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, check=False)
    return process.stdout.strip() if process.returncode == 0 else "unavailable"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_digest() -> str:
    digest = hashlib.sha256()
    files = sorted((ROOT / "src").rglob("*.rs"))
    files += [ROOT / "Cargo.toml", ROOT / "Cargo.lock"]
    for path in files:
        if path.is_file():
            digest.update(str(path.relative_to(ROOT)).encode())
            digest.update(b"\0")
            digest.update(path.read_bytes())
            digest.update(b"\0")
    return digest.hexdigest()


def summarize(records: list[dict]) -> dict:
    values = [record["elapsed_ms"] for record in records]
    return {
        "count": len(values),
        "median_ms": statistics.median(values),
        "min_ms": min(values),
        "max_ms": max(values),
        "median_user_cpu_ms": statistics.median(record["user_cpu_ms"] for record in records),
        "median_system_cpu_ms": statistics.median(record["system_cpu_ms"] for record in records),
    }


def run(args: argparse.Namespace) -> dict:
    load_at_start = os.getloadavg()
    binary = args.binary.resolve()
    if not binary.is_file():
        raise SemanticFailure(f"binary not found: {binary}; run cargo build --release first")
    manifest = args.manifest.resolve()
    cases = json.loads(manifest.read_text())
    jobs = []
    for case in cases:
        path = (manifest.parent / case["file"]).resolve()
        source = os.path.relpath(path, ROOT)
        for operation in ("check", "eval"):
            command = [str(binary), operation, source]
            if operation == "eval" and "fuel" in case:
                command += ["--fuel", str(case["fuel"])]
            jobs.append({
                "name": f'{case["name"]}/{operation}',
                "source": source,
                "source_sha256": sha256(path),
                "command": command,
                "expected": case[operation],
                "warmups": [],
                "samples": [],
            })
    # Complete the semantic gate before recording any benchmark sample.
    for job in jobs:
        job["preflight"] = invoke(job["command"], args.timeout)
        validate(job["preflight"], job["expected"], job["name"])
    for round_index in range(args.warmup + args.samples):
        # Reverse traversal every round so drift does not always favor one case.
        order = jobs if round_index % 2 == 0 else list(reversed(jobs))
        for job in order:
            result = invoke(job["command"], args.timeout)
            validate(result, job["expected"], job["name"])
            kind = "warmups" if round_index < args.warmup else "samples"
            job[kind].append(result)
    startup = []
    for _ in range(args.samples):
        result = invoke([str(binary), "--version"], args.timeout)
        validate(result, {"exit": 0}, "version control")
        if not result["stdout"].startswith("apl "):
            raise SemanticFailure(f"unexpected version response: {result}")
        startup.append(result)
    for job in jobs:
        job["summary"] = summarize(job["samples"])
        job["command"][0] = os.path.relpath(binary, ROOT)
    return {
        "schema": "apl-cli-baseline-v1",
        "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
        "measurement": "wall-clock CLI startup, file read, parsing, checking, and optional evaluation",
        "comparison": "initial baseline; no speedup or cross-language performance claim",
        "warmup_rounds": args.warmup,
        "sample_rounds": args.samples,
        "unexpected_failures": 0,
        "expected_nonzero_jobs": sum(job["expected"]["exit"] != 0 for job in jobs),
        "semantic_preflight": "all explicit outcomes checked before timing samples",
        "host": {"system": platform.system(), "release": platform.release(), "machine": platform.machine(),
                 "logical_cpus": os.cpu_count(), "load_average_at_start": load_at_start, "load_average_at_end": os.getloadavg()},
        "toolchain": capture(["rustc", "--version"]),
        "compiler_version": capture([str(binary), "--version"]),
        "binary_sha256": sha256(binary),
        "compiler_source_sha256": source_digest(),
        "git_revision": capture(["git", "rev-parse", "HEAD"]),
        "worktree_dirty": bool(capture(["git", "status", "--porcelain"])),
        "version_control": {"summary": summarize(startup), "samples": startup},
        "jobs": jobs,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=ROOT / "target/release/apl")
    parser.add_argument("--manifest", type=Path, default=ROOT / "benchmarks/cases/manifest.json")
    parser.add_argument("--output", type=Path, default=ROOT / "benchmarks/results/latest.json")
    parser.add_argument("--warmup", type=int, default=2)
    parser.add_argument("--samples", type=int, default=7)
    parser.add_argument("--timeout", type=float, default=10)
    args = parser.parse_args()
    if args.samples < 5 or args.warmup < 1 or args.timeout <= 0:
        parser.error("use at least five samples, one warmup, and a positive timeout")
    try:
        report = run(args)
    except (SemanticFailure, OSError, ValueError, KeyError) as error:
        print(f"baseline rejected: {error}", file=sys.stderr)
        return 1
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print("Initial CLI baseline (no comparative performance claim)")
    print("case                           median ms      min ms      max ms")
    for job in report["jobs"]:
        summary = job["summary"]
        print(f'{job["name"]:30} {summary["median_ms"]:10.3f} {summary["min_ms"]:11.3f} {summary["max_ms"]:11.3f}')
    print(f"Unexpected failures: 0; full outputs and samples: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
