"""Word-revision schemas with shared, unchanged strict transport/value helpers."""
from oracle import (Failure, Inconclusive, need, sha, strict, same, keys, natural,
                    decimal, profile, typed_value, heap_sites, outcome, assert_execution)
REVISION = "anl-words-v1"
PAIR_SCHEMA = "anl-words-pair-check-v1"
TRAPS = {"arithmetic_overflow", "division_by_zero", "invalid_shift", "invalid_length", "index_out_of_bounds"}
PAIR_EXITS = {"accepted": 0, "rejected": 1, "resource_limit": 3, "error": 4}

def validate_trace(document, expected_profile=None, sites=None, replay=False):
    keys(document, ("schema","semantic_revision","allocation_profile","events","completion"))
    need(document["schema"] == "anl-words-trace-v1", "trace schema")
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
