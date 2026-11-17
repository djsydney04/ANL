"""Strict artifact and finite-outcome comparisons for the memory validation gate."""
import copy
import hashlib
import json
import re

REVISION = "anl-owned-buffers-v1"
PAIR_SCHEMA = "anl-memory-pair-check-v1"
TRAPS = {"arithmetic_overflow", "division_by_zero", "invalid_length", "index_out_of_bounds"}
PAIR_EXITS = {"accepted": 0, "rejected": 1, "resource_limit": 3, "error": 4}


class Failure(RuntimeError):
    pass


class Inconclusive(Failure):
    pass


def need(condition, message):
    if not condition:
        raise Failure(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def strict(data):
    def members(pairs):
        result = {}
        for key, value in pairs:
            need(key not in result, "duplicate JSON member: " + key)
            result[key] = value
        return result
    def integer(value):
        need(value != "-0", "noncanonical JSON integer: -0")
        return int(value)
    def constant(value):
        raise Failure("non-JSON constant: " + value)
    try:
        if isinstance(data,(bytes,bytearray)):
            data=bytes(data).decode("utf-8",errors="strict")
        return json.loads(data, object_pairs_hook=members, parse_int=integer, parse_constant=constant)
    except (ValueError, UnicodeDecodeError) as error:
        raise Failure("invalid JSON: " + str(error)) from error


def same(actual, expected):
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(same(actual[k], v) for k, v in expected.items())
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(same(a, b) for a, b in zip(actual, expected))
    return actual == expected


def keys(value, expected):
    need(type(value) is dict and set(value) == set(expected), "unexpected object fields")


def natural(value):
    need(type(value) is int and 0 <= value < 2**64, "invalid natural JSON integer")
    return value


def decimal(value, signed=False):
    pattern = r"(?:0|[1-9][0-9]*)" if not signed else r"(?:0|[1-9][0-9]*|-[1-9][0-9]*)"
    need(type(value) is str and re.fullmatch(pattern, value) is not None, "noncanonical decimal")
    need(len(value) <= 20, "bounded counter/integer representation exceeded")
    number = int(value)
    if signed:
        need(-(2**63) <= number < 2**63, "i64 value out of range")
    return number


def profile(value):
    keys(value, ("abi","char_bits","i64_bytes","i64_align","size_bits","ptrdiff_bits"))
    need(value["abi"] == "anl-buffer-c11-v1", "profile ABI")
    for field in ("char_bits","i64_bytes","i64_align","size_bits","ptrdiff_bits"):
        need(type(value[field]) is int, "profile numeric field is not an integer")
    need(value["char_bits"] == 8 and value["i64_bytes"] == 8, "profile cell layout")
    need(value["i64_align"] in (1,2,4,8,16), "profile alignment")
    need(value["size_bits"] in (32,64) and value["ptrdiff_bits"] in (32,64), "profile width")
    return min(2**63-1, (2**value["size_bits"]-1)//8, (2**(value["ptrdiff_bits"]-1)-1)//8)


def typed_value(ty, value):
    if type(ty) is str:
        if ty == "i64":
            decimal(value, signed=True)
        elif ty == "bool":
            need(type(value) is bool, "bool value")
        elif ty == "unit":
            need(value is None, "unit value")
        else:
            raise Failure("unknown scalar type")
    else:
        keys(ty, ("tuple",))
        fields = ty["tuple"]
        need(type(fields) is list and 1 <= len(fields) <= 8, "tuple shape")
        need(type(value) is list and len(value) == len(fields), "tuple value shape")
        for child, item in zip(fields, value):
            need(type(child) is str, "nested tuple")
            typed_value(child, item)


def heap_sites(program):
    result = set()
    def walk(value, fid):
        if type(value) is dict:
            if value.get("tag") == "heap":
                result.add((fid, value["site"]))
            for child in value.values():
                walk(child, fid)
        elif type(value) is list:
            for child in value:
                walk(child, fid)
    for function in program["functions"]:
        walk(function["body"], function["id"])
    return result


def validate_trace(document, expected_profile=None, sites=None, replay=False):
    keys(document, ("schema","semantic_revision","allocation_profile","events","completion"))
    need(document["schema"] == "anl-memory-trace-v1", "trace schema")
    need(document["semantic_revision"] == REVISION, "trace revision")
    max_cells = profile(document["allocation_profile"])
    if expected_profile is not None:
        need(same(document["allocation_profile"], expected_profile), "trace profile differs")
    events = document["events"]
    need(type(events) is list and len(events) <= 65536, "trace event bound")
    next_request = next_empty = 0
    stack = []
    for event in events:
        need(type(event) is dict, "trace event is not an object")
        kind = event.get("kind")
        fields = {
            "request": ("kind","request","site","length","response"),
            "release": ("kind","request","site"),
            "empty_open": ("kind","empty","site"),
            "empty_close": ("kind","empty","site"),
        }
        need(kind in fields, "unknown trace event")
        keys(event, fields[kind])
        keys(event["site"], ("function","heap"))
        site = tuple(natural(event["site"][k]) for k in ("function","heap"))
        if sites is not None:
            need(site in sites, "trace site is not in program")
        if kind == "request":
            ordinal = decimal(event["request"])
            need(ordinal == next_request, "request ordinal is not consecutive")
            next_request += 1
            length = decimal(event["length"], signed=True)
            need(0 < length <= max_cells, "request length outside profile")
            need(event["response"] in ("success","refused"), "allocation response")
            if event["response"] == "success":
                stack.append(("positive", ordinal, site))
        elif kind == "empty_open":
            ordinal = decimal(event["empty"])
            need(ordinal == next_empty, "empty ordinal is not consecutive")
            next_empty += 1
            stack.append(("empty", ordinal, site))
        else:
            positive = kind == "release"
            ordinal = decimal(event["request" if positive else "empty"])
            expected = ("positive" if positive else "empty", ordinal, site)
            need(bool(stack) and stack[-1] == expected, "closure does not match live top owner")
            stack.pop()
    completion = document["completion"]
    need(type(completion) is dict, "trace completion")
    kind = completion.get("kind")
    if kind == "value":
        keys(completion, ("kind","type","value"))
        typed_value(completion["type"], completion["value"])
        need(completion["type"] == "i64", "executable trace result must be i64")
        need(not stack, "normal completion has live owners")
    elif kind == "trap":
        keys(completion, ("kind","trap"))
        need(completion["trap"] in TRAPS, "unknown source trap")
    elif kind == "resource_limit":
        keys(completion, ("kind",))
        need(not replay, "resource prefix is not a replay script")
    elif kind == "infrastructure":
        keys(completion, ("kind","reason"))
        need(type(completion["reason"]) is str, "infrastructure reason")
        need(not replay, "infrastructure prefix is not a replay script")
    else:
        raise Failure("unknown completion")
    return document


def assert_trace(actual_bytes, expected, sites=None):
    need(len(actual_bytes) <= 8388608, "trace byte bound")
    actual = validate_trace(strict(actual_bytes), expected["allocation_profile"], sites)
    need(same(actual, expected), "trace or completion differs from sealed oracle")
    return actual


def outcome(completion):
    kind = completion["kind"]
    if kind == "value":
        return dict(outcome="value", type=completion["type"], value=completion["value"])
    if kind == "trap":
        return dict(outcome="trap", trap=completion["trap"])
    if kind == "resource_limit":
        return dict(outcome="resource_limit")
    return dict(outcome="infrastructure_error", reason=completion["reason"])


def assert_execution(record, expected, wire=False, refusal_values=()):
    code = {"value":0, "trap":2, "resource_limit":3, "invalid_ir":1}[expected["outcome"]]
    if not wire and record["exit"] == 0 and expected["outcome"] == "value":
        for refusal in refusal_values:
            if record["stdout"] == (refusal + "\n").encode():
                raise Inconclusive("required default allocation-success observation absent")
    need(record["exit"] == code, "execution exit differs")
    if wire:
        need(same(strict(record["stdout"]), expected), "typed execution outcome differs")
    elif expected["outcome"] == "value":
        need(record["stdout"] == (expected["value"] + "\n").encode(), "source/native value differs")
        need(record["stderr"] == b"", "successful execution diagnostic")
    else:
        need(record["stdout"] == b"", "failed source/native execution published output")
        if "trap" in expected:
            need(expected["trap"].encode() in record["stderr"], "missing defined-trap classification")
        else:
            need(record["stderr"] != b"", "missing execution diagnostic")


def assert_pair_report(record, status, expected_profile):
    need(record["exit"] == PAIR_EXITS[status], "pair checker exit differs")
    report = strict(record["stdout"])
    keys(report, ("schema","status","semantic_revision","allocation_profile","reason"))
    need(report["schema"] == PAIR_SCHEMA and report["semantic_revision"] == REVISION,
         "pair report schema/revision")
    need(report["status"] == status, "pair checker status differs")
    need(type(report["reason"]) is str and len(report["reason"].encode("utf-8")) <= 1024,
         "pair reason bound/type")
    if status == "accepted":
        profile(report["allocation_profile"])
        need(same(report["allocation_profile"], expected_profile), "pair accepted profile")
        need(report["reason"] == "", "accepted pair reason must be empty")
    else:
        need(report["allocation_profile"] is None, "failed pair must not claim an input profile")
    return report

