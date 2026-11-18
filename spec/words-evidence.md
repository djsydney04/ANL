# Word artifacts and execution evidence

These interfaces use semantic revision `anl-words-v1` and the
[word Core/MIR definitions](words.md#core-v4-and-word-mir). The older
[memory protocols](memory-evidence.md) retain their original schema and trap
allowlists. The commands below expose model checks and finite execution; they
do not establish full compiler/native correctness or a qualified language release.

## Export actual artifacts

The existing developer exporter accepts checked word source and requires a fresh
output directory:

```sh
cargo run --release --locked --features memory-evidence --example memory_evidence -- examples/words/packed-fields.anl /tmp/anl-word-export
```

It also accepts an imported Core program with
`--core CORE_JSON OUT_DIR`. Imported v4 stays v4 even without word nodes; imported
Core has no invented source provenance. The manifest schema is
`anl-words-evidence-bundle-v1`, with exactly `schema`, `semantic_revision`,
`allocation_profile`, `has_memory`, `runtime`, `compiler`, `files`, `sources`.
File records bind byte counts and SHA256; compiler/source identity record shapes
are unchanged.

| Loaded graph | `has_memory` | `runtime` | Retained compiled inputs, besides the manifest |
| --- | --- | --- | --- |
| No memory form or view signature | `false` | `none` | `core.json`, `mir.json`, `program.c` |
| Any memory form or view signature | `true` | `default` | Those files plus `runtime.c`, `runtime.h` |

These are actual checked Core and lowered MIR used for the retained default C.
The mixed bundle retains the default allocator sources used by its build; it is
not an evidence-instrumented binary. `none` means no separate buffer runtime,
not absence of scalar helpers, libc or the host OS. The mandatory v4 profile
alone does not select a buffer runtime.

## Trace and replay activation

Only a `memory-evidence` feature build can activate `ANL_MEMORY_TRACE` and
`ANL_MEMORY_REPLAY`, and only for an actually memory-bearing loaded graph after
checking and entry selection. Pure-word graphs ignore both variables, even
malformed values, and create no trace. Default builds ignore them. Export,
check and verify do not activate them. Existing path protection, exclusive trace
creation, bounded replay snapshot and native build capture rules are unchanged.

Mixed word/buffer executions use `anl-words-trace-v1`; root fields remain exactly
`schema`, `semantic_revision`, `allocation_profile`, `events`, `completion`.
Event shapes and order remain request/release/empty-open/empty-close with paired
sites and separate positive/empty ordinal spaces. Word operations emit no new
heap event. The trap allowlist adds only `invalid_shift` to
`arithmetic_overflow`, `division_by_zero`, `invalid_length`, `index_out_of_bounds`.
Old traces reject that new tag. Normal completion values are still signed `i64`.

Exact replay checks the new schema, revision, profile, complete ordered event
vector and value/trap completion. A mismatch is infrastructure failure, not an
allocator refusal. Resource, administrative and infrastructure prefixes are not
completed replay evidence. An instrumentation failure exits 4 and must not select
a source heap-failure branch. Pure-word native runs have no applicable observed
trace; the formal model's event vector is empty. Pure-word comparisons therefore
compare captured values/traps, not a native trace that was never produced.

## Pair and raw checks

From `formal/`, the developer targets are:

```sh
lake build anl_words_raw_probe anl_words_pair_checker anl_words_reference_runner
```

From the repository root:

```sh
formal/.lake/build/bin/anl_words_raw_probe core /tmp/anl-word-export/core.json
formal/.lake/build/bin/anl_words_raw_probe mir /tmp/anl-word-export/mir.json
formal/.lake/build/bin/anl_words_pair_checker /tmp/anl-word-export/core.json /tmp/anl-word-export/mir.json
```

The raw probe accepts one mode (`core` or `mir`) and one file; it checks a whole
program without executing it. Pair accepts exactly two files and checks both
whole programs plus exact canonical lowering. It emits `anl-words-pair-check-v1`
with `schema`, `status`, `semantic_revision`, `allocation_profile`, `reason`.
Accepted exits 0 with the common profile and empty reason; rejection exits 1,
reader resource limit 3, invocation/I/O error 4. Unsuccessful pair reports have
null profile and do not establish either artifact's individual typing. Pair
acceptance is not a certificate for source parsing, generated C or a binary.

Core is bounded to 1 MiB, MIR to 8 MiB. The formal readers enforce logical Core
expression/MIR block depth 128 and JSON-container depth 1024 separately, exact
fields, duplicate rejection, canonical decimal values and uint64 JSON IDs.
Rust retains its smaller pinned parser boundary: 127 containers admitted, the
128th rejected as a parser resource limit. No identical admission-envelope or
universal round-trip claim is made.

## Bounded formal reference

Write a UTF-8 response plan, for example `responses.json`:

```json
{"schema":"anl-memory-response-plan-v1","responses":[],"default":"success"}
```

The unchanged plan has at most 65536 `success`/`refused` responses, a mandatory
default, and a 1 MiB byte bound. It defines a total abstract response stream;
it is not an exact native replay document. Unused entries are legal, and requests
past the vector consume the default response.

```sh
formal/.lake/build/bin/anl_words_reference_runner /tmp/anl-word-export/core.json responses.json 100000 262144
```

The four arguments are checked Core, response plan, expression/fill fuel, and
administrative transition budget. Fuel is canonical unsigned decimal in
`0..1000000000`; transitions in `0..262144`. Inputs are fully checked even at zero
budgets. Zero transitions cannot perform a pending allocation. The runner uses
the actual cumulative word `Tool.start?` and `Tool.run`; it has no separate
unmetered word evaluator.

A report is one `anl-words-reference-run-v1` JSON line with the same exact fields
as the [memory reference report](memory-evidence.md#formal-reference-runner):
`schema`, `status`, `semantic_revision`, `allocation_profile`, `fuel`,
`transition_budget`, `resource_reason`, `reason`, `meter`, `trace`.
Its trace uses the new word schema. Meter fields are `fuel_remaining`,
`active_slots`, `live_cells`, `tuple_fields`, `expression_depth`, before host
bookkeeping unwind.

| Status | Exit | Meaning |
| --- | --- | --- |
| `value` | 0 | Normal `i64` entry return |
| `trap` | 2 | One of the five defined traps, with retained world/trace |
| `resource_limit` | 3 | Depth, expression fuel, slots, live cells, fill fuel or tuple fields |
| `transition_limit` | 5 | Incomplete administrative prefix |
| `rejected` | 1 | Malformed input or invalid checked Core |
| `error` | 4 | Arguments, output limits, I/O or infrastructure |

Resource reasons are the exact tags `depth`, `expression_fuel`, `slots`,
`live_cells`, `fill_fuel`, `tuple_fields`. Administrative cutoff retains its
prefix with reason `administrative transition budget exhausted` and an
infrastructure trace completion. Neither is a semantic trap or completed replay.
Reports/traces are bounded to 8 MiB including final LF; trace export is capped at
65536 events, paths at 4096 UTF-8 bytes and diagnostics at 1024 bytes. Output
failure is infrastructure failure. Missing or partial output is incomplete
evidence, never an accepted result.

The [formal inventory](../formal/PROOFS.md#unsigned-word-model) separates accepted
machine/lowering proofs from byte/JSON/IO and compiled-tool trust boundaries. Byte/JSON/IO,
compiled Lean execution, Rust and C/native correctness remain explicit trust
boundaries. This increment makes no performance or ANL OS implementation claim.
