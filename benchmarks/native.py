#!/usr/bin/env python3
"""Measure native build, warmed executable, and interpreter costs at an exact source revision."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile

from run import ROOT, SemanticFailure, capture, invoke, sha256, summarize, validate


DEFAULT_REVISION = "19d726cca188f04229e0962f4d903be3ebf4a9cb"


def record(report: dict, command: list[str], expected: dict | None,
           context: str, timeout: float) -> dict:
    row = {"context": context, "command": command}
    report["invocations"].append(row)
    try:
        row.update(invoke(command, timeout))
        if expected is not None:
            validate(row, expected, context)
        elif row["exit"] != 0:
            raise SemanticFailure(f"{context}: setup command failed: {row}")
    except (SemanticFailure, OSError) as error:
        row["failure"] = str(error)
        raise
    return row


def require_same(expected: dict, observed: dict, context: str) -> None:
    if expected != observed:
        changed = sorted(name for name in expected.keys() | observed.keys()
                         if expected.get(name) != observed.get(name))
        raise SemanticFailure(f"{context} changed: {changed}")


def compiler_inputs(revision: str) -> dict:
    names = subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", revision, "--", "src", "Cargo.toml",
         "Cargo.lock", "rust-toolchain.toml", ".cargo"], cwd=ROOT, text=True).splitlines()
    if not names:
        raise SemanticFailure(f"no compiler inputs found at {revision}")
    expected = {name: hashlib.sha256(subprocess.check_output(
        ["git", "show", f"{revision}:{name}"], cwd=ROOT)).hexdigest() for name in names}
    actual_names = {str(path.relative_to(ROOT)) for path in (ROOT / "src").rglob("*.rs")}
    actual_names |= {name for name in names if not name.startswith("src/")}
    actual = {name: sha256(ROOT / name) for name in actual_names}
    require_same(expected, actual, "compiler inputs versus pinned Git tree")
    return actual


def binary_info(path: Path) -> dict:
    return {"bytes": path.stat().st_size, "sha256": sha256(path)}


def run(args: argparse.Namespace, report: dict) -> None:
    revision = subprocess.check_output(
        ["git", "rev-parse", f"{args.revision}^{{commit}}"], cwd=ROOT, text=True).strip()
    cc = shutil.which(os.environ.get("CC", "cc"))
    cargo = shutil.which("cargo")
    rustc = shutil.which("rustc")
    if not all((cc, cargo, rustc)):
        raise SemanticFailure("cargo, rustc, and a C11 compiler (CC or cc) must be on PATH")
    manifest = ROOT / "benchmarks/cases/native-manifest.json"
    cases = json.loads(manifest.read_text())
    inputs = {manifest, Path(__file__), ROOT / "benchmarks/run.py"}
    for case in cases:
        inputs.update((manifest.parent / name).resolve() for name in case["inputs"])
    fixture_hashes = {str(path.relative_to(ROOT)): sha256(path) for path in sorted(inputs)}
    source_hashes = compiler_inputs(revision)
    cc_version = capture([cc, "--version"])
    tool_paths = {Path(tool).resolve() for tool in (cc, cargo, rustc)}
    for name, executable in (("cargo", cargo), ("rustc", rustc)):
        if Path(executable).resolve().name == "rustup":
            tool_paths.add(Path(subprocess.check_output(
                [str(Path(executable).resolve()), "which", name], cwd=ROOT, text=True).strip()))
    installed_dir = re.search(r"^InstalledDir: (.+)$", cc_version, re.MULTILINE)
    if installed_dir and (Path(installed_dir[1]) / "clang").is_file():
        tool_paths.add((Path(installed_dir[1]) / "clang").resolve())
    linker = capture([cc, "-print-prog-name=ld"])
    if Path(linker).is_file():
        tool_paths.add(Path(linker).resolve())
    tool_hashes = {str(path): sha256(path) for path in sorted(tool_paths)}
    report.update({
        "source_revision": revision,
        "git_head_at_start": capture(["git", "rev-parse", "HEAD"]),
        "compiler_inputs_before": source_hashes,
        "benchmark_inputs_before": fixture_hashes,
        "host": {"system": platform.system(), "release": platform.release(), "machine": platform.machine(),
                 "logical_cpus": os.cpu_count(), "load_average_at_start": os.getloadavg()},
        "tools": {"rustc": capture([rustc, "--version"]), "cargo": capture([cargo, "--version"]),
                  "cc": cc_version, "linker": linker, "python": sys.version,
                  "executable_sha256_before": tool_hashes},
        "warmup_rounds": args.warmup, "sample_rounds": args.samples,
        "cases": [], "jobs": [],
    })
    with tempfile.TemporaryDirectory(prefix="apl-native-baseline-") as directory:
        scratch = Path(directory)
        build_dir = scratch / "cargo"
        record(report, [cargo, "build", "--release", "--locked", "--offline", "--target-dir", str(build_dir)],
               None, "fresh release compiler build (setup)", args.build_timeout)
        binary = build_dir / "release/apl"
        report["compiler_binary"] = binary_info(binary)
        report["compiler_version"] = capture([str(binary), "--version"])
        artifacts = {}
        for case in cases:
            source = str((manifest.parent / case["file"]).resolve().relative_to(ROOT))
            executable = scratch / case["name"]
            built = scratch / f'{case["name"]}-build-sample'
            record(report, [str(binary), "build", source, "-o", str(executable)],
                   {"exit": 0, "stdout": ""}, case["name"] + "/initial-build", args.timeout)
            first = record(report, [str(executable)], case["expected"],
                           case["name"] + "/first-launch", args.timeout)
            artifacts[str(executable)] = binary_info(executable)
            item = {"name": case["name"], "source": source, "expected": case["expected"],
                    "executable": artifacts[str(executable)], "first_launch": first}
            report["cases"].append(item)
            interpreter = [str(binary), "eval", source]
            if "fuel" in case:
                interpreter += ["--fuel", str(case["fuel"])]
            for operation, command, expected in [
                ("build", [str(binary), "build", source, "-o", str(built)], {"exit": 0, "stdout": ""}),
                ("native", [str(executable)], case["expected"]),
                ("interpreter", interpreter, case["expected"]),
            ]:
                report["jobs"].append({"name": case["name"] + "/" + operation,
                                       "operation": operation, "command": command, "expected": expected,
                                       "built_output": str(built), "value_expected": case["expected"],
                                       "warmups": [], "samples": []})
        for round_index in range(-1, args.warmup + args.samples):
            phase = "preflight" if round_index == -1 else "warmups" if round_index < args.warmup else "samples"
            order = report["jobs"] if round_index % 2 == 0 else list(reversed(report["jobs"]))
            for job in order:
                result = record(report, job["command"], job["expected"], f'{job["name"]}/{phase}', args.timeout)
                if job["operation"] == "build":
                    result["artifact"] = binary_info(Path(job["built_output"]))
                    result["execution_check"] = record(report, [job["built_output"]], job["value_expected"],
                                                       f'{job["name"]}/{phase}/artifact-check', args.timeout)
                if phase == "preflight":
                    job[phase] = result
                else:
                    job[phase].append(result)
        for job in report["jobs"]:
            job["summary"] = summarize(job["samples"])
        report["binary_disassembly"] = []
        disassembler = shutil.which("otool") or shutil.which("objdump")
        if disassembler:
            option = "-tvV" if Path(disassembler).name == "otool" else "-d"
            for item in report["cases"]:
                if item["name"].startswith("fibonacci-"):
                    report["binary_disassembly"].append(record(
                        report, [disassembler, option, str(scratch / item["name"])], {"exit": 0},
                        item["name"] + "/binary-disassembly", args.timeout))
        require_same(report["compiler_binary"], binary_info(binary), "compiler binary")
        require_same(artifacts, {path: binary_info(Path(path)) for path in artifacts}, "warmed native artifacts")
        report["assembly_evidence"] = []
        for case in cases:
            if not case["name"].startswith("fibonacci-"):
                continue
            source = str((manifest.parent / case["file"]).resolve().relative_to(ROOT))
            emitted = record(report, [str(binary), "emit-c", source], {"exit": 0}, case["name"] + "/emit-c", args.timeout)
            c_file, asm_file = scratch / "program.c", scratch / "program.s"
            c_file.write_text(emitted["stdout"])
            record(report, [cc, "-std=c11", "-O2", "-S", str(c_file), "-o", str(asm_file)],
                   {"exit": 0, "stdout": ""}, case["name"] + "/assembly", args.timeout)
            report["assembly_evidence"].append({"case": case["name"], "c_sha256": sha256(c_file),
                                                "assembly_sha256": sha256(asm_file), "assembly": asm_file.read_text()})
    after_source = compiler_inputs(revision)
    after_fixtures = {name: sha256(ROOT / name) for name in fixture_hashes}
    after_tools = {name: sha256(Path(name)) for name in tool_hashes}
    require_same(source_hashes, after_source, "compiler inputs during run")
    require_same(fixture_hashes, after_fixtures, "benchmark inputs during run")
    require_same(tool_hashes, after_tools, "tool executables during run")
    report.update({"compiler_inputs_after": after_source, "benchmark_inputs_after": after_fixtures,
                   "tool_executable_sha256_after": after_tools,
                   "git_head_at_end": capture(["git", "rev-parse", "HEAD"]),
                   "completed_at_utc": datetime.now(timezone.utc).isoformat(),
                   "unexpected_failures": 0, "status": "accepted"})
    report["host"]["load_average_at_end"] = os.getloadavg()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--revision", default=DEFAULT_REVISION)
    parser.add_argument("--output", type=Path, default=ROOT / "benchmarks/results/native-local.json")
    parser.add_argument("--warmup", type=int, default=2)
    parser.add_argument("--samples", type=int, default=7)
    parser.add_argument("--timeout", type=float, default=15)
    parser.add_argument("--build-timeout", type=float, default=120)
    args = parser.parse_args()
    if args.samples < 5 or args.warmup < 1 or args.timeout <= 0 or args.build_timeout <= 0:
        parser.error("use at least five samples, one warmup, and positive timeouts")
    report = {"schema": "apl-native-baseline-v1", "status": "running", "invocations": [],
              "started_at_utc": datetime.now(timezone.utc).isoformat(),
              "measurement": "whole native build, warmed native process, and interpreter CLI wall/CPU time",
              "limitations": "shared host; warm filesystem caches; no cold-cache, memory, cross-language, or general speedup claim"}
    try:
        run(args, report)
    except (SemanticFailure, OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        report.update({"status": "rejected", "failure": str(error), "unexpected_failures": 1})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    if report["status"] != "accepted":
        print(f'baseline rejected: {report["failure"]}; partial evidence: {args.output}', file=sys.stderr)
        return 1
    for job in report["jobs"]:
        s = job["summary"]
        print(f'{job["name"]:32} {s["median_ms"]:9.3f} ms [{s["min_ms"]:.3f}, {s["max_ms"]:.3f}]')
    print(f'Validated {len(report["invocations"])} invocations; evidence: {args.output}')
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
