#!/usr/bin/env python3
"""Check local-state semantics through the real source, core, and formal CLIs.

Finite expectations are hand-derived from spec/control-flow.md. The explicit
budget probes count resource outcomes as inconclusive semantic comparisons:
Rust counts expression entries and Lean counts abstract-machine transitions.
"""
import argparse
import copy
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REVISION = "local-state-2026-11-17"
INVALID = {"outcome": "invalid_ir"}
RESOURCE = {"outcome": "resource_limit"}
EXIT = {"value": 0, "invalid_ir": 1, "trap": 2, "resource_limit": 3}


def value(v, ty="i64"):
    return {"outcome": "value", "type": ty, "value": str(v) if ty == "i64" else v}


def trap(kind):
    return {"outcome": "trap", "trap": kind}


def lit(v=None, ty="i64"):
    node = {"tag": {"i64": "integer", "bool": "boolean", "unit": "unit"}[ty], "ty": ty}
    if ty != "unit":
        node["value"] = str(v) if ty == "i64" else v
    return node


def local(index, ty="i64"):
    return {"tag": "local", "ty": ty, "index": index}


def bind(initial, body, mutable=True):
    return {"tag": "let_mut" if mutable else "let", "ty": body["ty"], "value": initial, "body": body}


def assign(index, rhs):
    return {"tag": "assign", "ty": "unit", "index": index, "value": rhs}


def loop(condition, body):
    return {"tag": "while", "ty": "unit", "condition": condition, "body": body}


def branch(condition, yes, no):
    return {"tag": "if", "ty": yes["ty"], "condition": condition, "then": yes, "else": no}


def binary(op, left, right, ty="i64"):
    return {"tag": "binary", "ty": ty, "op": op, "left": left, "right": right}


def call(function, arguments, ty="i64"):
    return {"tag": "call", "ty": ty, "function": function, "arguments": arguments}


def fixture(expression):
    return {"schema": "apl-expr-v1", "semantic_revision": REVISION, "expression": expression}


def function(index, name, body, params=()):
    return {"id": index, "name": name, "params": list(params), "result": body["ty"], "body": body}


def program(functions, entry=0):
    return {"schema": "apl-core-v1", "semantic_revision": REVISION, "functions": functions, "entry": entry}


# Each literal expectation distinguishes a state-flow failure, rather than merely
# requiring two implementations to agree with each other.
SOURCES = [
    ("outer changes survive scope pop", "fn main()->i64 {let mut x=1; {x=x+2;}; x}", value(3)),
    ("immutable read is a value snapshot", "fn main()->i64 {let mut x=1; let old=x; x=3; old*10+x}", value(13)),
    ("operands see current state in order", "fn main()->i64 {let mut x=1; let a={x=3;x}+{x=x+4;x}; a*10+x}", value(107)),
    ("left operand snapshot survives right write", "fn main()->i64 {let mut x=2; let y=x*{x=5;x}; y*10+x}", value(105)),
    ("initializer threads state before binding", "fn main()->i64 {let mut x=1; let mut y={x=4;x+2}; y=y+1; x*10+y}", value(47)),
    ("selected branch receives condition state", "fn main()->i64 {let mut x=0; if {x=2;true} {x=x+1;} else {x=99;}; x}", value(3)),
    ("shadow scope removes only its own cell", "fn main()->i64 {let mut x=1; {let mut x=2; x=99;}; x}", value(1)),
    ("assignment reacquires target after rhs scope", "fn main()->i64 {let mut x=1; x={let mut y=9; x=x+2; let z=y; x+z}; x}", value(12)),
    ("final false condition retains effects", "fn main()->i64 {let mut x=0; while({x=x+1;x<4}) {} x}", value(4)),
    ("body effects reach next condition", "fn main()->i64 {let mut x=0; while({x=x+1;x<10}) {x=x+2;} x}", value(10)),
    ("zero iterations skip trapping body", "fn main()->i64 {let mut x=7; while(false) {x=1/0;} x}", value(7)),
    ("each loop body gets fresh locals", "fn main()->i64 {let mut i=0; let mut total=0; while(i<10) {let mut n=0; n=n+1; total=total+n; i=i+1;} total}", value(10)),
    ("nested loops isolate their locals", "fn main()->i64 {let mut i=0; let mut sum=0; while(i<3) {let mut j=0; while(j<4) {let mut x=i+j; x=x+1; sum=sum+x; j=j+1;} i=i+1;} sum}", value(42)),
    ("Boolean and unit cells retain scalar types", "fn main()->i64 {let mut b=true; let mut u=(); let mut x=0; while(b) {u={x=x+1;()}; b=false;} if u==() && !b {x+10} else {0}}", value(11)),
    ("short circuits retain only left effects", "fn main()->i64 {let mut x=0; {x=x+1;false} && {x=99;true}; {x=x+2;true} || {x=99;false}; x}", value(3)),
    ("final short circuit guard preserves effects", "fn main()->i64 {let mut x=0; let mut n=0; while({n=n+1;n<4} && {x=x+10;true}) {x=x+1;} n*100+x}", value(433)),
    ("arguments snapshot left to right", "fn pack(a:i64,b:i64,c:i64)->i64 {100*a+10*b+c} fn main()->i64 {let mut x=1; pack({x=x+1;x},{x=x*3;x},{x=x+1;x})*10+x}", value(2677)),
    ("callee cells never alias caller or each other", "fn change(a:i64,b:i64)->i64 {let mut a=a; a=99; a*100+b} fn main()->i64 {let mut x=7; let y=change(x,x); y*10+x}", value(99077)),
    ("nested calls restore post-argument caller", "fn inc(a:i64)->i64 {let mut a=a; a=a+10;a} fn pair(a:i64,b:i64)->i64 {a*100+b} fn main()->i64 {let mut x=1; let y=pair(inc({x=x+1;x}),inc({x=x+2;x})); y*10+x}", value(12144)),
    ("recursive mutable frames remain isolated", "fn sum(n:i64)->i64 {let mut answer=n; if n>0 {answer=answer+sum(n-1);} else {}; answer} fn main()->i64 {sum(10)}", value(55)),
    ("unused mutable function selects v1", "fn unused()->unit {let mut x=0;} fn main()->i64 {42}", value(42)),
    ("condition trap takes precedence", "fn main()->i64 {let mut x=0; while({x=x+1;1/0==0}) {9223372036854775807+1;} x}", trap("division_by_zero")),
    ("body trap skips later overflow", "fn main()->i64 {let mut x=0; while(x<1) {x=x+1;1/0;9223372036854775807+1;} x}", trap("division_by_zero")),
    ("final condition overflow is observed", "fn main()->i64 {let mut x=9223372036854775806; while({x=x+1;true}) {} 0}", trap("arithmetic_overflow")),
    ("rhs trap prevents later expressions", "fn main()->i64 {let mut x=0; x={let mut y=9223372036854775807;y=y+1;1/0}; x}", trap("arithmetic_overflow")),
    ("first argument trap skips later mutation", "fn f(x:i64)->i64 {let mut y=x;y=y+1;y} fn pair(a:i64,b:i64)->i64 {a+b} fn main()->i64 {let mut x=0; pair(f({x=2;1/0}),{x=9223372036854775807;x+1})}", trap("division_by_zero")),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust", type=Path, required=True, help="production apl executable")
    parser.add_argument("--formal", type=Path, default=ROOT / "formal/.lake/build/bin/apl_formal")
    args = parser.parse_args()
    rust, formal = args.rust.resolve(), args.formal.resolve()
    for executable in (rust, formal):
        if not executable.is_file():
            parser.error(f"required executable does not exist: {executable}")
    counts = {"finite": 0, "invalid": 0, "resource": 0, "inconclusive": 0}

    with tempfile.TemporaryDirectory(prefix="apl-local-state-") as directory:
        path, source = Path(directory) / "case.json", Path(directory) / "case.apl"

        def invoke(command):
            return subprocess.run([str(part) for part in command], capture_output=True, timeout=45)

        def check(name, document, oracle, fuel=100000, allow_resource=False, exact=None):
            raw = document if isinstance(document, bytes) else (document if isinstance(document, str) else json.dumps(document)).encode()
            path.write_bytes(raw)
            observed = []
            for label, command in [("Rust", [rust, "eval-core", path]), ("Lean", [formal, path])]:
                result = invoke([*command, "--fuel", fuel])
                try:
                    outcome = json.loads(result.stdout)
                except (ValueError, UnicodeDecodeError) as error:
                    raise AssertionError((name, label, "non-JSON outcome", result.returncode, result.stdout, result.stderr)) from error
                assert outcome.get("outcome") in EXIT, (name, label, outcome)
                assert result.returncode == EXIT[outcome["outcome"]], (name, label, result.returncode, outcome, result.stderr)
                expected = exact[label] if exact else oracle
                if not (allow_resource and outcome == RESOURCE and exact is None):
                    assert outcome == expected, (name, label, outcome, expected, raw, result.stderr)
                observed.append(outcome)
            if allow_resource and RESOURCE in observed:
                counts["inconclusive"] += 1
            elif oracle == INVALID:
                counts["invalid"] += 1
            elif oracle == RESOURCE:
                counts["resource"] += 1
            else:
                counts["finite"] += 1

        def check_source(name, text, oracle, fuel=100000):
            source.write_text(text)
            dumped = invoke([rust, "dump-core", source])
            assert dumped.returncode == 0, (name, "source export", dumped.stderr)
            document = json.loads(dumped.stdout)
            assert (document["schema"], document["semantic_revision"]) == ("apl-core-v1", REVISION), (name, document)
            evaluated = invoke([rust, "eval", source, "--fuel", fuel])
            assert evaluated.returncode == EXIT[oracle["outcome"]], (name, "source evaluation", evaluated.stderr)
            if oracle["outcome"] == "value":
                assert evaluated.stdout.decode() == oracle["value"] + "\n", (name, evaluated.stdout, oracle)
            else:
                assert oracle["trap"] in evaluated.stderr.decode(), (name, evaluated.stderr)
            check(name, dumped.stdout, oracle, fuel)

        for name, text, oracle in SOURCES:
            check_source(name, text, oracle)
        check_source("300000 iterations do not accumulate call depth", "fn main()->i64 {let mut i=0; while(i<300000) {i=i+1;} i}", value(300000), fuel=20000000)

        unit, false, true = lit(None, "unit"), lit(False, "bool"), lit(True, "bool")
        # Handwritten core checks bypass source lowering and its discarded lets.
        check("v1 integer lower bound", fixture(lit(-(1 << 63))), value(-(1 << 63)))
        check("v1 integer upper bound", fixture(lit((1 << 63) - 1)), value((1 << 63) - 1))
        check("direct assignment yields unit", fixture(bind(lit(1), assign(0, lit(9)))), value(None, "unit"))
        check("direct assignment state survives discarded let", fixture(bind(lit(1), bind(assign(0, lit(9)), local(1), False))), value(9))
        check("initializer cannot see new shadow cell", fixture(bind(lit(4), bind(local(0), local(0)))), value(4))
        check("outer permission survives inner immutable scope", fixture(bind(lit(1), bind(lit(2), bind(assign(1, lit(9)), local(2), False), False))), value(9))
        check("while false returns unit", fixture(loop(false, unit)), value(None, "unit"))
        # A name other than main may be the nullary i64 entry; params reverse at entry.
        check("imported entry and parameter order", program([function(0, "subtract", binary("sub", local(1), local(0)), ["i64", "i64"]), function(1, "start", call(0, [lit(7), lit(2)]))], 1), value(5))

        invalid_terms = [
            ("unbound assignment", assign(0, lit(1))),
            ("out of scope assignment", bind(lit(1), assign(1, lit(2)))),
            ("immutable ordinary let", bind(lit(1), assign(0, lit(2)), False)),
            ("immutable shadow blocks outer permission", bind(lit(1), bind(lit(2), assign(0, lit(3)), False))),
            ("assignment type mismatch", bind(lit(1), assign(0, true))),
            ("initializer is checked in outer context", bind(local(0), unit)),
            ("unused branch permission checked", bind(lit(1), branch(false, assign(0, lit(2)), unit), False)),
            ("unselected branch binding checked", branch(false, assign(0, lit(2)), unit)),
            ("loop condition must be Boolean", loop(lit(1), unit)),
            ("unreached loop body must be unit", loop(false, lit(1))),
            ("body local unavailable in condition", loop(local(0, "bool"), bind(true, unit))),
            ("calls forbidden in expression fixture", call(0, [])),
            ("dead calls forbidden in expression fixture", branch(true, lit(1), call(0, []))),
            ("mismatched branch types", branch(true, lit(1), unit)),
            ("bad unary operand", {"tag": "unary", "ty": "i64", "op": "neg", "operand": true}),
            ("bad binary operand", binary("add", true, lit(1))),
        ]
        for name, expression in invalid_terms:
            check(name, fixture(expression), INVALID)
        for expression in [bind(lit(1), unit), assign(0, lit(1)), loop(false, unit)]:
            valid = fixture(bind(lit(0), expression))
            for field in expression:
                bad = copy.deepcopy(valid)
                del bad["expression"]["body"][field]
                check(f"missing {expression['tag']}.{field}", bad, INVALID)
            bad = copy.deepcopy(valid)
            bad["expression"]["body"]["extra"] = True
            check(f"extra {expression['tag']} field", bad, INVALID)
            bad = copy.deepcopy(valid)
            bad["expression"]["body"]["ty"] = "i64"
            check(f"forged {expression['tag']} result", bad, INVALID)

        valid = fixture(bind(lit(0), assign(0, lit(1))))
        for schema, revision in [("apl-expr-v0", REVISION), ("apl-expr-v1", "m1-2026-11-16"), ("apl-expr-v0", "m1-2026-11-16"), ("apl-expr-v2", REVISION), ("apl-expr-v1", "unknown")]:
            bad = copy.deepcopy(valid)
            bad.update(schema=schema, semantic_revision=revision)
            check("schema and revision boundary", bad, INVALID)
        for raw in [b"", b"\xff", b"null", b"[]", b"{}", b"{", b"{} {}"]:
            check("malformed document", raw, INVALID)
        raw = json.dumps(valid, separators=(",", ":"))
        for spelling in ["0.0", "0e0", "-0", "-1", "+0", "00", "4294967296", "18446744073709551615", '"0"', "true"]:
            check("invalid assignment index representation", raw.replace('"index":0', '"index":' + spelling), INVALID)
        for original, replacement in [('"index":0', '"index":0,"index":0'), ('"index":0', '"index":0,"ind\\u0065x":0'), ('"schema":"apl-expr-v1"', '"schema":"apl-expr-v1","schema":"apl-expr-v1"'), ('"tag":"assign"', '"tag":"assign","tag":"assign"')]:
            check("duplicate JSON object member", raw.replace(original, replacement), INVALID)
        for spelling in ["01", "-0", "+1", "1.0", str(1 << 63), str(-(1 << 63) - 1)]:
            check("invalid integer scalar encoding", fixture(lit(spelling)), INVALID)
        for mutate in [lambda p: p.update(extra=True), lambda p: p.pop("semantic_revision"), lambda p: p["expression"].update(tag="unknown"), lambda p: p["expression"].update(ty="unknown")]:
            bad = copy.deepcopy(valid)
            mutate(bad)
            check("strict document and constructor fields", bad, INVALID)

        base = program([function(0, "main", lit(42))])
        for mutate in [lambda p: p.update(entry=1), lambda p: p["functions"][0].update(id=1), lambda p: p["functions"][0].update(name="fn"), lambda p: p["functions"][0].update(name="é"), lambda p: p["functions"][0].update(result="bool"), lambda p: p["functions"][0].update(params=["i64"]), lambda p: p["functions"][0].update(extra=1), lambda p: p["functions"][0].pop("body")]:
            bad = copy.deepcopy(base)
            mutate(bad)
            check("function table and entry validation", bad, INVALID)
        check("duplicate function names", program([function(0, "main", lit(42)), function(1, "main", lit(0))]), INVALID)
        check("unused parameter assignment forbidden", program([function(0, "main", lit(42)), function(1, "unused", assign(0, lit(2)), ["i64"])]), INVALID)
        check("unused function cannot read caller locals", program([function(0, "main", bind(lit(42), local(0))), function(1, "unused", local(0))]), INVALID)
        for arguments in [[], [true], [lit(1), lit(2)]]:
            check("call arity and argument types", program([function(0, "main", call(1, arguments)), function(1, "identity", local(0), ["i64"])]), INVALID)
        check("unknown function reference", program([function(0, "main", call(99, []))]), INVALID)
        for key in ("id", "entry"):
            text = json.dumps(base, separators=(",", ":"))
            check(f"noninteger {key}", text.replace(f'"{key}":0', f'"{key}":0e0'), INVALID)

        # Fixed v0 fixtures still execute unchanged, and their old constructors
        # also work when explicitly placed in the new semantic revision.
        for name in ("core-expression.json", "core-program.json"):
            old = json.loads((ROOT / "spec/fixtures" / name).read_text())
            check("v0 compatibility " + name, old, value(42))
            old["schema"] = old["schema"].replace("v0", "v1")
            old["semantic_revision"] = REVISION
            check("v0 constructors in v1 " + name, old, value(42))

        # Resource behavior is asserted per CLI where their budget definitions differ.
        empty = fixture(loop(false, unit))
        check("zero budget cannot enter state term", valid, RESOURCE, fuel=0, allow_resource=True)
        check("while false below either budget", empty, value(None, "unit"), fuel=1, allow_resource=True)
        check("while false Rust entry cost differs from transitions", empty, value(None, "unit"), fuel=2, allow_resource=True, exact={"Rust": value(None, "unit"), "Lean": RESOURCE})
        check("terminal state accepted at final transition", empty, value(None, "unit"), fuel=3)
        check("infinite loop spends finite budget", fixture(loop(true, unit)), RESOURCE, fuel=50, allow_resource=True)
        check("input byte bound", " " * 1048577, RESOURCE)
        check("JSON nesting bound", "[" * 1000 + "]" * 1000, RESOURCE)

    print(f"local-state CLI: {counts['finite']} finite cases, {counts['invalid']} rejections, "
          f"{counts['resource']} input limits passed; {counts['inconclusive']} resource comparisons inconclusive")


if __name__ == "__main__":
    main()
