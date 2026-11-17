#!/usr/bin/env python3
"""Compare flat-product CLIs with independent finite and malformed expectations.

The fixture manifest includes source exports, hand-authored core artifacts and
old scalar embeddings. Resource results check each tool's own boundary and are
inconclusive semantic comparisons: Rust expression fuel and Lean transitions,
JSON depth, allocation and slot limits are not interchangeable.
"""
import argparse
import copy
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REVISION = "flat-products-2026-11-17"
EXIT = {"value": 0, "invalid_ir": 1, "trap": 2, "resource_limit": 3}
RESOURCE = {"outcome": "resource_limit"}


def exact_json(actual, expected):
    """Keep Boolean/number, unit/singleton and tuple shape distinctions exact."""
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(
            exact_json(actual[key], value) for key, value in expected.items()
        )
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(
            exact_json(a, b) for a, b in zip(actual, expected)
        )
    return actual == expected


def unique_members(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON member: {key}")
        result[key] = value
    return result


def expr(term):
    return {"schema": "apl-expr-v2", "semantic_revision": REVISION, "expression": term}


def case_bytes(case):
    """Generate large/deep probes without committing padded fixture files."""
    if "document" in case:
        return case["document"].encode()
    kind = case["generator"]
    if kind == "invalid_utf8":
        return b"\xff"
    if kind == "spaces":
        return b" " * case["bytes"]
    if kind == "json_depth":
        return ("[" * case["depth"] + "0" + "]" * case["depth"]).encode()
    if kind == "expression_depth":
        term = {"tag": "boolean", "ty": "bool", "value": True}
        for _ in range(case["operators"]):
            term = {"tag": "unary", "op": "not", "operand": term, "ty": "bool"}
        return json.dumps(expr(term), separators=(",", ":")).encode()
    if kind == "padded_scalar":
        raw = json.dumps(expr({"tag": "integer", "ty": "i64", "value": "42"}),
                         separators=(",", ":")).encode()
        return raw + b" " * (case["bytes"] - len(raw))
    raise AssertionError(f"unknown fixture generator: {kind}")


def check_oracle():
    expected = {"outcome": "value", "type": {"tuple": ["i64", "bool", "unit"]},
                "value": ["42", True, None]}
    mutations = []
    for index, value in [(0, 42), (1, 1), (2, False), (2, [])]:
        bad = copy.deepcopy(expected)
        bad["value"][index] = value
        mutations.append(bad)
    bad = copy.deepcopy(expected)
    bad["value"].pop()
    mutations.append(bad)
    bad = copy.deepcopy(expected)
    bad["value"].append(None)
    mutations.append(bad)
    bad = copy.deepcopy(expected)
    bad["type"]["tuple"][0] = "bool"
    mutations.append(bad)
    bad = copy.deepcopy(expected)
    bad["value"] = {"0": "42", "1": True, "2": None}
    mutations.append(bad)
    assert all(not exact_json(bad, expected) for bad in mutations)
    assert not exact_json({"outcome": "value", "type": "unit", "value": None},
                          {"outcome": "value", "type": {"tuple": ["unit"]}, "value": [None]})
    return len(mutations) + 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust", type=Path, required=True)
    parser.add_argument("--formal", type=Path, default=ROOT / "formal/.lake/build/bin/apl_formal_v2")
    parser.add_argument("--old-formal", type=Path, default=ROOT / "formal/.lake/build/bin/apl_formal")
    parser.add_argument("--report", type=Path, help="optional JSON command and outcome evidence")
    args = parser.parse_args()
    rust, formal, old_formal = (p.resolve() for p in (args.rust, args.formal, args.old_formal))
    for executable in (rust, formal, old_formal):
        if not executable.is_file():
            parser.error(f"required executable does not exist: {executable}")
    manifest = json.loads((ROOT / "formal/fixtures/flat-products.json").read_text())
    assert manifest["schema"] == "apl-flat-products-tests-v1"
    counts = {"finite": 0, "invalid": 0, "resource_boundaries": 0, "inconclusive": 0,
              "source_exports": 0, "old_scalar_embeddings": 0, "revision_checks": 0}
    records, results = [], []

    def invoke(command):
        result = subprocess.run([str(part) for part in command], capture_output=True, timeout=45)
        records.append({"command": [str(part) for part in command], "exit": result.returncode,
                        "stdout": result.stdout.decode(errors="replace"),
                        "stderr": result.stderr.decode(errors="replace")})
        return result

    def check_result(name, label, command, expected):
        result = invoke(command)
        try:
            actual = json.loads(result.stdout, object_pairs_hook=unique_members)
        except (ValueError, UnicodeDecodeError) as error:
            raise AssertionError((name, label, "invalid JSON outcome", records[-1])) from error
        assert result.returncode == EXIT[expected["outcome"]], (name, label, expected, records[-1])
        assert exact_json(actual, expected), (name, label, expected, records[-1])
        return actual

    with tempfile.TemporaryDirectory(prefix="apl-flat-products-") as directory:
        path, source = Path(directory) / "case.json", Path(directory) / "case.apl"
        for case in manifest["cases"]:
            name, expected = case["name"], case["expected"]
            if "source" in case:
                source.write_text(case["source"])
                observed = invoke([rust, "eval", source, "--fuel", case.get("source_fuel", 100000)])
                assert observed.returncode == EXIT[expected["outcome"]], (name, records[-1])
                if expected["outcome"] == "value":
                    assert observed.stdout == (expected["value"] + "\n").encode(), (name, records[-1])
                else:
                    assert observed.stdout == b"" and expected["trap"].encode() in observed.stderr, (name, records[-1])
                exported = invoke([rust, "dump-core", source])
                assert exported.returncode == 0 and not exported.stderr, (name, records[-1])
                document = json.loads(exported.stdout, object_pairs_hook=unique_members)
                assert (document["schema"], document["semantic_revision"]) == ("apl-core-v2", REVISION), (name, document)
                path.write_bytes(exported.stdout)
                counts["source_exports"] += 1
            else:
                path.write_bytes(case_bytes(case))
            fuel = case.get("fuel", 100000)
            rust_expected = case.get("rust_expected", expected)
            actual_rust = check_result(name, "Rust", [rust, "eval-core", path, "--fuel", fuel], rust_expected)
            actual_lean = check_result(name, "Lean", [formal, path, "--fuel", fuel], expected)
            if exact_json(expected, RESOURCE) or exact_json(rust_expected, RESOURCE):
                classification = "resource_inconclusive"
                counts["resource_boundaries"] += 1
                counts["inconclusive"] += 1
            elif expected["outcome"] == "invalid_ir":
                classification = "invalid"
                counts["invalid"] += 1
            else:
                classification = "finite"
                counts["finite"] += 1
            results.append({"name": name, "classification": classification,
                            "rust": actual_rust, "lean": actual_lean})
            if "revision" in case:
                revision = invoke([formal, path, "--revision"])
                assert revision.returncode == 0 and revision.stdout == (case["revision"] + "\n").encode(), (name, records[-1])
                counts["revision_checks"] += 1
            if "lean_followup" in case:
                followup = case["lean_followup"]
                check_result(name, "Lean sufficient transitions", [formal, path, "--fuel", followup["fuel"]], followup["expected"])
            if "old_document" in case:
                path.write_text(case["old_document"])
                check_result(name, "old Rust schema", [rust, "eval-core", path, "--fuel", 100000], expected)
                check_result(name, "old Lean adapter", [old_formal, path, "--fuel", 100000], expected)
                counts["old_scalar_embeddings"] += 1
        # Invalid typing is rejected before execution, even with no transition budget.
        forged = expr({"tag": "integer", "ty": "bool", "value": "42"})
        path.write_text(json.dumps(forged))
        for label, command in [("Rust", [rust, "eval-core", path]), ("Lean", [formal, path])]:
            check_result("type-before-fuel", label, [*command, "--fuel", 0], {"outcome": "invalid_ir"})
        for fuel in ["-1", "1e2", "+1", "1000000001", "", "١"]:
            result = invoke([formal, path, "--fuel", fuel])
            assert result.returncode == 4 and not result.stdout, ("invalid CLI fuel", fuel, records[-1])
    oracle_checks = check_oracle()
    summary = {"status": "PASS", "cases": len(results), **counts,
               "type_before_fuel_checks": 2, "invalid_cli_fuel_checks": 6,
               "oracle_corruptions_rejected": oracle_checks, "commands": len(records)}
    if args.report:
        args.report.write_text(json.dumps({"summary": summary, "cases": results, "commands": records}, indent=2) + "\n")
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
