#!/usr/bin/env python3
"""Compare verified coverage and whole-CLI cost with explicit outcome gates."""
from __future__ import annotations

import argparse
import copy
from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import shutil
import signal
import subprocess
import tempfile
import time

from run import ROOT, SemanticFailure, sha256, summarize

MANIFEST = ROOT / "benchmarks/cases/verification/manifest.json"
BASELINE_REVISION = "f8ffb5f128aab5eaed4db3770ae500cd923cc61c"
CANDIDATE_REVISION = "5e9dff071bf58a369af0386fb042c5948dcf8862"
BASELINE_SHA = "1e35c9f20f41efbf91e910ae710784b619d3194575366ffa8e06029b3610f274"
CANDIDATE_SHA = "6f40884213529b053b542b20849f7e8da29762b340365ab6ec7d936f12810efd"
SOLVER_SHA = "9b3df8db3324ac2de9ebdd2841477366ecad0626656f806c2168ebf2732745a4"
CODES = {"verified": 0, "failed": 5, "unknown": 6, "unsupported": 7}


def require(condition, message):
    if not condition:
        raise SemanticFailure(message)


def capture(command):
    return subprocess.check_output(command, cwd=ROOT, text=True, timeout=10).strip()


def execute(command):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.perf_counter_ns()
    child = subprocess.Popen([str(x) for x in command], cwd=ROOT, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        stdout, stderr = child.communicate(timeout=40)
    except subprocess.TimeoutExpired as error:
        os.killpg(child.pid, signal.SIGKILL)
        child.communicate()
        raise SemanticFailure(f"command exceeded 40 seconds: {command}") from error
    elapsed = (time.perf_counter_ns() - started) / 1_000_000
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    return {"command": [str(x) for x in command], "exit": child.returncode,
            "stdout": stdout, "stderr": stderr, "elapsed_ms": elapsed,
            "user_cpu_ms": (after.ru_utime - before.ru_utime) * 1000,
            "system_cpu_ms": (after.ru_stime - before.ru_stime) * 1000}


def compiler_inputs(revision):
    names = capture(["git", "ls-tree", "-r", "--name-only", revision, "--", "src",
                     "Cargo.toml", "Cargo.lock", "rust-toolchain.toml", ".cargo"]).splitlines()
    require(bool(names), f"no compiler inputs at {revision}")
    return {name: hashlib.sha256(subprocess.check_output(
        ["git", "show", f"{revision}:{name}"], cwd=ROOT)).hexdigest() for name in names}


def load_cases():
    cases = json.loads(MANIFEST.read_text())
    inputs = [MANIFEST, Path(__file__), ROOT / "benchmarks/run.py"]
    for case in cases:
        if "generate" in case:
            width = case["generate"]["unit_parameters"]
            branches = case["generate"]["branches"]
            require(1 <= width <= 8000 and 1 <= branches <= 95, "invalid generated workload")
            params = ",".join(f"p{i}:unit" for i in range(width))
            arguments = ",".join(f"p{i}" for i in range(width))
            case["source"] = (f"fn leaf({params})->unit{{let mut x=();"
                              + "if true{}else{};" * branches
                              + f"x}}\nfn caller({params})->unit{{leaf({arguments})}}\n")
        else:
            path = MANIFEST.parent / case["file"]
            inputs.append(path)
            case["source"] = path.read_text()
    return cases, {str(path.relative_to(ROOT)): sha256(path) for path in inputs}


def normalize(report):
    result = copy.deepcopy(report)
    if result["compiler"]:
        for key in ["executable", "executable_path_bytes_hex", "sha256"]:
            result["compiler"][key] = "<compiler identity>"
    result["scope"]["model_proof"] = "<descriptive proof scope>"
    for query in result["obligations"]:
        query["query"] = re.sub(r"\(set-option :timeout [0-9]+\)",
                                "(set-option :timeout <remaining>)", query["query"])
        query["query_sha256"] = hashlib.sha256(query["query"].encode()).hexdigest()
    return result


def validate(row, case, variant, tools, path):
    report = row["report"]
    state = case["name"].startswith("state-")
    status = "unsupported" if state and variant == "baseline" else case["status"]
    require(row["exit"] == CODES[status] and report["status"] == status,
            f"{case['name']}/{variant}: wrong outcome")
    require(len(report["sources"]) == 1, "wrong source count")
    source = report["sources"][0]
    require(source["sha256"] == sha256(path) and source["bytes"] == path.stat().st_size
            and source["path"] == str(path.resolve()), "source identity mismatch")
    require(report["schema"] == ("apl-verify-v1" if state and variant == "candidate"
                                 else "apl-verify-v0"), "wrong report schema")
    require(report["semantic_revision"] == ("local-state-2026-11-17" if state
                                            else "m1-2026-11-16"), "wrong semantics")
    if state and variant == "candidate":
        require(report["verification_revision"] == "apl-state-verify-v1", "wrong verification rules")
    queries = report["obligations"]
    if status == "unsupported":
        require(not queries and report["compiler"] is None and report["solver"] is None,
                "unsupported case invoked tools or invented queries")
        if variant == "candidate":
            require(report["expanded_nodes"] == 0, "unsupported case entered generation")
    else:
        require(report["compiler"]["sha256"] == tools[variant]["sha256"]
                and report["solver"]["sha256"] == tools["solver"]["sha256"], "tool identity mismatch")
        require(len(queries) == case["queries"], "wrong query count")
        for index, query in enumerate(queries):
            require(query["id"] == index and query["query_complete"], "incomplete or reordered query")
            require(query["query_sha256"] == hashlib.sha256(query["query"].encode()).hexdigest(),
                    "query hash mismatch")
            require(query["status"] in ["verified", "failed"]
                    and query["solver_status"] in ["sat", "unsat"], "unfinished query")
            function = report["functions"][query["function_id"]]
            expected = [(i, f"p{i}", ty) for i, ty in enumerate(function["parameter_types"])
                        if ty != "unit"]
            if state:
                require(query["model_symbols"] == [
                    {"symbol": symbol, "type": ty, "origin": {"kind": "parameter", "index": i}}
                    for i, symbol, ty in expected], "incomplete parameter manifest")
            model = query["model"]
            if query["solver_status"] == "sat":
                require(isinstance(model, dict), "SAT query is missing its model")
                require(isinstance(model.get("assignments"), list), "model assignments are absent")
                require(model["replayed"] is False, "unexpected replay claim")
                require([(a["parameter"], a["symbol"], a["type"]) for a in model["assignments"]]
                        == expected, "incomplete model")
                for assignment in model["assignments"]:
                    value = assignment["value"]
                    valid = (type(value) is bool if assignment["type"] == "bool"
                             else isinstance(value, str) and -(2**63) <= int(value) < 2**63)
                    require(valid, "invalid scalar model value")
            else:
                require(model is None, "UNSAT query must not carry a model")
        if status == "verified":
            require(all(q["status"] == "verified" for q in queries), "unsuccessful proof query")
        if status == "failed":
            require(any(q["status"] == "failed" and q["kind"] == case["failed_kind"] for q in queries),
                    "expected refutation missing")
        if status == "unknown":
            require(report["message"] == "symbolic work exceeds 1000000 units"
                    and all(q["function"] == "leaf" and q["status"] == "verified" for q in queries),
                    "wrong resource boundary or lost completed work")
    return {"status": status, "query_count": len(queries),
            "query_bytes": sum(len(q["query"].encode()) for q in queries),
            "expanded_nodes": report.get("expanded_nodes", 0),
            "function_count": len(report["functions"])}


def verify(case, variant, tools, path):
    row = execute([tools[variant]["path"], "verify", path, "--json", "--solver",
                   tools["solver"]["path"], "--timeout-ms", "30000"])
    row["report"] = json.loads(row["stdout"])
    row["metrics"] = validate(row, case, variant, tools, path)
    return row


def gate_sensitivity(row, case, tools, path):
    mutations = ["wrong outcome", "broken query hash", "incomplete query", "missing SAT model"]
    sat_index = next((i for i, query in enumerate(row["report"]["obligations"])
                      if query["solver_status"] == "sat"), None)
    require(sat_index is not None, "gate sensitivity requires a real SAT query")
    for name in mutations:
        changed = copy.deepcopy(row)
        if name == "wrong outcome":
            changed["report"]["status"] = "failed"
        elif name == "broken query hash":
            changed["report"]["obligations"][0]["query_sha256"] = "0" * 64
        elif name == "incomplete query":
            changed["report"]["obligations"][0]["query_complete"] = False
        else:
            changed["report"]["obligations"][sat_index]["model"] = None
        try:
            validate(changed, case, "candidate", tools, path)
        except SemanticFailure:
            continue
        raise SemanticFailure(f"gate accepted {name}")
    return mutations


def run(args, report):
    tools = {}
    for name in ["baseline", "candidate", "solver"]:
        raw = getattr(args, name)
        path = Path(shutil.which(str(raw)) or raw).resolve()
        digest = sha256(path)
        require(digest == getattr(args, name + "_sha256"), f"unexpected {name} binary hash")
        tools[name] = {"path": str(path), "sha256": digest}
    cases, inputs = load_cases()
    sources = {"baseline": compiler_inputs(args.baseline_revision),
               "candidate": compiler_inputs(args.candidate_revision)}
    require(all(sha256(args.candidate_source / name) == digest for name, digest in sources["candidate"].items()),
            "current compiler inputs differ from candidate revision")
    report.update(tools=tools, cases=cases, benchmark_inputs_before=inputs,
                  source_inputs=sources, baseline_revision=args.baseline_revision,
                  candidate_revision=args.candidate_revision, candidate_source=str(args.candidate_source.resolve()),
                  solver_version=capture([tools["solver"]["path"], "-version"]))
    with tempfile.TemporaryDirectory(prefix="apl-verification-benchmark-") as directory:
        scratch = Path(directory)
        paths = {}
        for case in cases:
            path = scratch / (case["name"] + ".apl")
            path.write_text(case["source"])
            paths[case["name"]] = path
            pair = []
            for variant in ["baseline", "candidate"]:
                row = verify(case, variant, tools, path)
                row.update(case=case["name"], variant=variant, phase="preflight")
                report["invocations"].append(row)
                pair.append(row)
            if case["name"].startswith("pure-"):
                require(normalize(pair[0]["report"]) == normalize(pair[1]["report"]),
                        "pure report or query meaning changed")
            if case["name"] == "pure-affine":
                report["gate_sensitivity"] = gate_sensitivity(pair[1], case, tools, path)
            checks = [(arguments, expected, False) for arguments, expected in case.get("eval", [])]
            if case.get("trap"):
                checks.append(("", None, True))
            for arguments, expected, trap in checks:
                oracle = scratch / "oracle.apl"
                oracle.write_text(case["source"] + f"\nfn main()->i64{{f({arguments})}}\n")
                for variant in ["baseline", "candidate"]:
                    row = execute([tools[variant]["path"], "eval", oracle])
                    valid = (row["exit"] == 2 and "arithmetic_overflow" in row["stderr"] if trap
                             else row["exit"] == 0 and row["stdout"] == f"{expected}\n" and not row["stderr"])
                    require(valid, f"{case['name']}: independent runtime oracle failed")
                    row.update(case=case["name"], variant=variant, expected=expected, trap=trap,
                               source=oracle.read_text(), source_sha256=sha256(oracle))
                    report["validation_invocations"].append(row)
        if not args.gate_only:
            for round_number in range(6):
                phase = "warmup" if round_number == 0 else "sample"
                order = cases if round_number % 2 == 0 else list(reversed(cases))
                variants = ["baseline", "candidate"] if round_number % 2 == 0 else ["candidate", "baseline"]
                for case in order:
                    for variant in variants:
                        row = verify(case, variant, tools, paths[case["name"]])
                        row.update(case=case["name"], variant=variant, phase=phase, round=round_number)
                        report["invocations"].append(row)
            report["summaries"] = []
            for case in cases:
                for variant in ["baseline", "candidate"]:
                    rows = [x for x in report["invocations"]
                            if x["case"] == case["name"] and x["variant"] == variant]
                    metrics = [{k: v for k, v in x["metrics"].items() if k != "query_bytes"} for x in rows]
                    require(all(m == metrics[0] for m in metrics), "work or outcomes changed across rounds")
                    samples = [x for x in rows if x["phase"] == "sample"]
                    report["summaries"].append({"case": case["name"], "variant": variant,
                                                "metrics": rows[0]["metrics"], "timing": summarize(samples)})
        require(all(path.read_text() == case["source"] for case in cases
                    for path in [paths[case["name"]]]), "workload source changed during measurement")
    report["tool_sha256_after"] = {name: sha256(Path(tool["path"])) for name, tool in tools.items()}
    require(report["tool_sha256_after"] == {name: tool["sha256"] for name, tool in tools.items()},
            "tool binary changed during measurement")
    report["benchmark_inputs_after"] = {name: sha256(ROOT / name) for name in inputs}
    require(report["benchmark_inputs_after"] == inputs, "benchmark inputs changed")
    report["source_inputs_after"] = {name: sha256(args.candidate_source / name) for name in sources["candidate"]}
    require(report["source_inputs_after"] == sources["candidate"], "compiler inputs changed")
    report["host"]["load_average_at_end"] = os.getloadavg()
    report.update(status="accepted", unexpected_failures=0,
                  completed_at_utc=datetime.now(timezone.utc).isoformat())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--baseline-sha256", default=BASELINE_SHA)
    parser.add_argument("--candidate-sha256", default=CANDIDATE_SHA)
    parser.add_argument("--solver-sha256", default=SOLVER_SHA)
    parser.add_argument("--baseline-revision", default=BASELINE_REVISION)
    parser.add_argument("--candidate-revision", default=CANDIDATE_REVISION)
    parser.add_argument("--candidate-source", type=Path, default=ROOT)
    parser.add_argument("--gate-only", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT / "target/verification-local.json.gz")
    args = parser.parse_args()
    report = {"schema": "apl-verification-measurement-v2", "status": "running",
              "started_at_utc": datetime.now(timezone.utc).isoformat(), "invocations": [],
              "validation_invocations": [], "comparison": "coverage and whole-CLI cost; no speedup claim",
              "warmup_rounds": 1, "sample_rounds": 5, "gate_only": args.gate_only,
              "host": {"system": platform.system(), "release": platform.release(),
                       "machine": platform.machine(), "logical_cpus": os.cpu_count(),
                       "load_average_at_start": os.getloadavg()}}
    try:
        run(args, report)
    except (SemanticFailure, OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        report.update(status="rejected", unexpected_failures=1, error=str(error))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(args.output, "wt") as output:
        json.dump(report, output, indent=2)
    print(json.dumps({"status": report["status"], "verification_invocations": len(report["invocations"]),
                      "oracle_invocations": len(report["validation_invocations"]),
                      "error": report.get("error"), "output": str(args.output)}, indent=2))
    return 0 if report["status"] == "accepted" else 1


if __name__ == "__main__":
    raise SystemExit(main())
