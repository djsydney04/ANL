#!/usr/bin/env python3
"""Exercise real import/evaluation CLIs against explicit and generated oracles."""
import argparse
import copy
import json
import random
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOW, HIGH = -(1 << 63), (1 << 63) - 1
REV = "m1-2026-11-16"


def lit(value, ty="i64"):
    tag = {"i64": "integer", "bool": "boolean", "unit": "unit"}[ty]
    result = {"tag": tag, "ty": ty}
    if ty != "unit":
        result["value"] = str(value) if ty == "i64" else value
    return result


def binary(op, left, right, ty="i64"):
    return dict(tag="binary", ty=ty, op=op, left=left, right=right)


def fixture(e):
    return dict(schema="apl-expr-v0", semantic_revision=REV, expression=e)


def value(v, ty="i64"):
    return dict(outcome="value", type=ty, value=str(v) if ty == "i64" else v)


def trap(kind):
    return dict(outcome="trap", trap=kind)


class ArithmeticTrap(Exception):
    pass


def bounded(n):
    if n < LOW or n > HIGH:
        raise ArithmeticTrap("arithmetic_overflow")
    return n


def interpret(e, env=()):
    tag = e["tag"]
    if tag == "integer":
        return int(e["value"])
    if tag == "boolean":
        return e["value"]
    if tag == "unit":
        return None
    if tag == "local":
        return env[e["index"]]
    if tag == "let":
        return interpret(e["body"], (interpret(e["value"], env),) + env)
    if tag == "if":
        return interpret(e["then"] if interpret(e["condition"], env) else e["else"], env)
    if tag == "unary":
        a = interpret(e["operand"], env)
        return bounded(-a) if e["op"] == "neg" else not a
    a = interpret(e["left"], env)
    op = e["op"]
    if op == "and" and not a:
        return False
    if op == "or" and a:
        return True
    b = interpret(e["right"], env)
    if op == "add":
        return bounded(a + b)
    if op == "sub":
        return bounded(a - b)
    if op == "mul":
        return bounded(a * b)
    if op in ("div", "rem"):
        if b == 0:
            raise ArithmeticTrap("division_by_zero")
        if a == LOW and b == -1:
            raise ArithmeticTrap("arithmetic_overflow")
        q = a // b
        if (a < 0) != (b < 0) and a % b:
            q += 1
        return q if op == "div" else a - q * b
    return {"lt": lambda: a < b, "le": lambda: a <= b,
            "gt": lambda: a > b, "ge": lambda: a >= b,
            "eq": lambda: a == b, "ne": lambda: a != b,
            "and": lambda: a and b, "or": lambda: a or b}[op]()


def expected(e):
    try:
        return value(interpret(e), e["ty"])
    except ArithmeticTrap as error:
        return trap(str(error))


def generate(rng, ty, depth, env=()):
    choices = ["literal", "local"] if depth == 0 else ["literal", "local", "let", "if", "op"]
    choice = rng.choice(choices)
    matching = [i for i, t in enumerate(env) if t == ty]
    if choice == "local" and matching:
        return dict(tag="local", ty=ty, index=rng.choice(matching))
    if choice in ("literal", "local"):
        return lit(rng.choice([LOW, HIGH, -7, -3, -1, 0, 1, 2, 3, 7]), ty) if ty == "i64" else lit(rng.choice([True, False]) if ty == "bool" else None, ty)
    if choice == "let":
        bound = rng.choice(["i64", "bool", "unit"])
        return dict(tag="let", ty=ty, value=generate(rng, bound, depth - 1, env),
                    body=generate(rng, ty, depth - 1, (bound,) + env))
    if choice == "if":
        return {"tag": "if", "ty": ty, "condition": generate(rng, "bool", depth - 1, env),
                "then": generate(rng, ty, depth - 1, env), "else": generate(rng, ty, depth - 1, env)}
    if ty == "unit":
        return lit(None, "unit")
    ops = ["neg", "add", "sub", "mul", "div", "rem"] if ty == "i64" else ["not", "lt", "le", "gt", "ge", "eq", "ne", "and", "or"]
    op = rng.choice(ops)
    input_ty = ty if op in ("neg", "not", "and", "or") else rng.choice(["i64", "bool", "unit"]) if op in ("eq", "ne") else "i64"
    a = generate(rng, input_ty, depth - 1, env)
    if op in ("neg", "not"):
        return dict(tag="unary", ty=ty, op=op, operand=a)
    return binary(op, a, generate(rng, input_ty, depth - 1, env), ty)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--rust", type=Path, help="also compare the production CLI and source exporter")
    args = parser.parse_args()
    lean = ROOT / "formal/.lake/build/bin/apl_formal"
    rust = args.rust.resolve() if args.rust else None
    count = 0
    with tempfile.TemporaryDirectory(prefix="apl-formal-") as directory:
        path = Path(directory) / "case.json"

        def check(document, oracle, fuel=100000, compare=True):
            nonlocal count
            raw = document if isinstance(document, bytes) else (document if isinstance(document, str) else json.dumps(document)).encode()
            path.write_bytes(raw)
            commands = [[str(lean), str(path), "--fuel", str(fuel)]]
            if rust and compare:
                commands.append([str(rust), "eval-core", str(path), "--fuel", str(fuel)])
            code = {"value": 0, "trap": 2, "resource_limit": 3, "invalid_ir": 1}[oracle["outcome"]]
            for command in commands:
                run = subprocess.run(command, capture_output=True, timeout=15)
                assert run.returncode == code, (command, run.returncode, run.stdout, run.stderr, raw)
                assert json.loads(run.stdout) == oracle, (command, run.stdout, oracle, raw)
            count += 1

        for name in ("core-expression.json", "core-program.json"):
            check((ROOT / "spec/fixtures" / name).read_bytes(), value(42))
        boundary = [LOW, LOW + 1, -7, -3, -1, 0, 1, 3, 7, HIGH - 1, HIGH]
        for op in ("add", "sub", "mul", "div", "rem", "lt", "le", "gt", "ge", "eq", "ne"):
            for a, b in [(LOW, -1), (LOW, 0), (HIGH, 1), (HIGH, 2), (0, LOW), (LOW, HIGH), (-7, 3), (7, -3), (-7, -3), (7, 3)]:
                e = binary(op, lit(a), lit(b), "i64" if op in ("add", "sub", "mul", "div", "rem") else "bool")
                check(fixture(e), expected(e))
        for n in boundary:
            e = dict(tag="unary", ty="i64", op="neg", operand=lit(n))
            check(fixture(e), expected(e))
        fault = binary("div", lit(1), lit(0))
        overflow = binary("add", lit(HIGH), lit(1))
        predicate_fault = binary("eq", fault, lit(0), "bool")
        for op, first in [("and", False), ("or", True)]:
            check(fixture(binary(op, lit(first, "bool"), predicate_fault, "bool")), value(first, "bool"))
        check(fixture(binary("add", fault, overflow)), trap("division_by_zero"))
        check(fixture(binary("add", overflow, fault)), trap("arithmetic_overflow"))
        check(fixture(dict(tag="let", ty="i64", value=fault, body=lit(42))), trap("division_by_zero"))
        for ty, v in [("unit", None), ("bool", True), ("i64", 7)]:
            for op in ("eq", "ne"):
                check(fixture(binary(op, lit(v, ty), lit(v, ty), "bool")), value(op == "eq", "bool"))
        rng = random.Random(20261116)
        for _ in range(180):
            e = generate(rng, rng.choice(["i64", "bool", "unit"]), 4)
            check(fixture(e), expected(e))
        invalid = dict(outcome="invalid_ir")
        base = fixture(lit(42))
        for raw in [b"\xff", b"", b"null", b"[]", b"{}", b"{", b"{} {}"]:
            check(raw, invalid)
        for field, new in [("schema", "unknown"), ("semantic_revision", "unknown"), ("extra", 1)]:
            bad = copy.deepcopy(base)
            bad[field] = new
            check(bad, invalid)
        for field, new in [("ty", "bool"), ("tag", "unknown"), ("extra", 1), ("value", "01"), ("value", "-0"), ("value", "+1"), ("value", str(HIGH + 1)), ("value", str(LOW - 1)), ("value", 42), ("value", "1.0")]:
            bad = copy.deepcopy(base)
            bad["expression"][field] = new
            check(bad, invalid)
        raw = json.dumps(base)
        check(raw.replace('"ty": "i64"', '"ty":"i64","ty":"i64"'), invalid)
        check(raw.replace('"ty": "i64"', '"ty":"i64","t\\u0079":"i64"'), invalid)
        check(fixture(dict(tag="local", ty="i64", index=0)), invalid)
        for index in ["0.0", "0e0", "-0", "1e99999999"]:
            local = '{"tag":"local","ty":"i64","index":' + index + '}'
            expr = '{"tag":"let","ty":"i64","value":{"tag":"integer","ty":"i64","value":"42"},"body":' + local + '}'
            check('{"schema":"apl-expr-v0","semantic_revision":"' + REV + '","expression":' + expr + '}', invalid)
        check(fixture(binary("add", lit(True, "bool"), lit(2))), invalid)
        check(fixture(binary("eq", lit(None, "unit"), lit(False, "bool"), "bool")), invalid)
        check(base, dict(outcome="resource_limit"), fuel=0)
        huge = copy.deepcopy(base)
        huge["expression"]["value"] = "1" * 100000
        check(huge, invalid)
        check(" " * 1048577, dict(outcome="resource_limit"))
        check("[" * 1000 + "]" * 1000, dict(outcome="resource_limit"))
        program = json.loads((ROOT / "spec/fixtures/core-program.json").read_text())
        for mutate in [lambda p: p.update(entry=99), lambda p: p["functions"][0].update(id=99), lambda p: p["functions"][0].update(name="fn"), lambda p: p["functions"][0].update(result="bool"), lambda p: p["functions"][0].update(params=["i64"])]:
            bad = copy.deepcopy(program)
            mutate(bad)
            check(bad, invalid)
        if rust:
            sources = [
                ("fn f(n:i64)->i64 { if n == 0 { 1 } else { n * f(n-1) } } fn main()->i64 { f(10) }", value(3628800)),
                ("fn even(n:i64)->bool { if n==0 { true } else { odd(n-1) } } fn odd(n:i64)->bool { if n==0 { false } else { even(n-1) } } fn main()->i64 { if even(20) { 42 } else { 0 } }", value(42)),
                ("fn pick(a:i64,b:i64)->i64 { a - b } fn main()->i64 { let x=100; pick(7,2) }", value(5)),
                ("fn pick(a:i64,b:i64)->i64 { a } fn main()->i64 { pick(1/0,9223372036854775807+1) }", trap("division_by_zero")),
                ("fn pick(a:i64,b:i64)->i64 { a } fn main()->i64 { pick(9223372036854775807+1,1/0) }", trap("arithmetic_overflow")),
                ("fn u()->unit {} fn b()->bool { u()==() } fn main()->i64 { if b() { 42 } else { 0 } }", value(42)),
                ("fn main()->i64 { let x=7; 0; { let x=x+1; x; }; x }", value(7)),
                ("fn loop()->i64 { loop() } fn main()->i64 { loop() }", dict(outcome="resource_limit")),
            ]
            source = Path(directory) / "case.apl"
            for text, oracle in sources:
                source.write_text(text)
                dumped = subprocess.run([str(rust), "dump-core", str(source)], capture_output=True, timeout=15)
                assert dumped.returncode == 0, dumped.stderr
                check(dumped.stdout, oracle)
            for example in sorted((ROOT / "examples").glob("*.apl")):
                dumped = subprocess.run([str(rust), "dump-core", str(example)], capture_output=True, timeout=15)
                assert dumped.returncode == 0, dumped.stderr
                run = subprocess.run([str(rust), "eval", str(example)], capture_output=True, timeout=15)
                assert run.returncode == 0, run.stderr
                check(dumped.stdout, value(int(run.stdout)))
    print(f"{count} formal CLI cases passed" + (" with Rust comparison" if rust else ""))


if __name__ == "__main__":
    main()
