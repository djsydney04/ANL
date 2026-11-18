# Owned-buffer evidence protocols

This document describes the executable evidence interfaces for
[`anl-owned-buffers-v1`](owned-buffers.md). They connect checked artifacts and
observed executions. They do not certify the Rust implementation, C compiler,
allocator, JSON parser, filesystem or host runtime.

The cumulative [unsigned-word revision](words.md) adds ordinary word values and
new schema IDs without widening this historical revision. Its
[word artifact protocols](words-evidence.md) apply to v4 programs; buffer cells,
resource permissions and evaluation order remain unchanged.

## Builds and artifact export

The ordinary compiler has no memory tracing or replay behavior. The
`memory-evidence` Cargo feature enables the evidence controls. Build the two
variants separately when comparing them:

```sh
cargo build --release --locked --target-dir target/default
cargo build --release --locked --features memory-evidence --target-dir target/memory-evidence
```

The exporter uses the production checked Core and MIR. It requires a fresh output
directory and writes `core.json`, `mir.json`, `program.c`, `runtime.c`, `runtime.h`
and a manifest:

```sh
cargo run --release --locked --features memory-evidence --example memory_evidence -- examples/buffers/basic.anl /tmp/anl-buffer-export
```

The exported C bundle uses the default runtime. Export does not activate tracing
or replay. The [MIR pair checker](memory-mir.md#independent-pair-checking) checks
the actual exported documents rather than a parallel handcrafted translation.

## Trace and exact native replay

Only an evidence-enabled compiler recognizes `ANL_MEMORY_TRACE` and
`ANL_MEMORY_REPLAY`. The controls activate for `eval`, `eval-core`, `build` and
`run` after the loaded graph has been checked, a memory-bearing graph has been
identified, and an executable entry has been selected. `check`, `verify`,
`dump-core`, `emit-c`, and the exporter ignore them. Scalar and tuple-only graphs
also ignore them, including malformed values. A default build ignores both
variables. With neither variable present, an evidence build uses ordinary
behavior.

`ANL_MEMORY_TRACE` must be a nonempty absolute path whose parent exists and whose
final entry does not exist. Trace creation is exclusive; existing files and
symlinks are rejected. `ANL_MEMORY_REPLAY` optionally names an existing regular
UTF-8 trace file. Replay without a trace path, empty values, embedded NULs, paths
over 4096 bytes and protected-path aliases are infrastructure errors. Replay is
read as a bounded snapshot. Native builds embed the validated replay plan and
trace path; generated programs do not parse replay JSON or reread these
environment variables. Running the same built program again with its already
created trace path fails rather than overwriting evidence.

Replay accepts a complete `value` or `trap` trace, and checks the exact ordered
events, sites, lengths and responses. It is distinct from the total response plan
used by the formal reference runner below. An unused or mismatched replay event
at completion is an error. If replay forces success but host backing cannot be
obtained, the result is an infrastructure error, not semantic allocator refusal.
A resource-limited interpreter run retains its valid prefix and is incomplete;
it need not consume the whole replay plan.

The evidence layer limits a trace or replay document to 8 MiB and its event vector
to 65,536 events. Instrumentation failures exit 4 and do not select the source
heap failure branch. These bounds are separate from interpreter language-resource
accounting and from host allocator refusal.

## Trace document

The root has exactly `schema`, `semantic_revision`, `allocation_profile`,
`events`, and `completion`. The schema is `anl-memory-trace-v1`; the revision and
profile are those of the checked program. Each site is an exact object with
unsigned integer fields `function` and `heap`.

| Event | Additional exact fields |
| --- | --- |
| `request` | `request`, `site`, `length`, `response` |
| `release` | `request`, `site` |
| `empty_open` | `empty`, `site` |
| `empty_close` | `empty`, `site` |

Each event has the indicated string `kind`. Request and empty ordinals are
canonical unsigned uint64 decimal strings in separate namespaces. Each namespace
starts at zero and advances consecutively. `length` is a positive canonical
signed-i64 decimal string for requests; `response` is `success` or `refused`.
An eligible positive allocation consumes one request even when refused. A
zero-length activation consumes an empty ordinal and no allocator response.
Target-rejected sizes emit no allocation event. A normal close pairs the exact
site and identity in lexical LIFO order. Traps retain the prefix without invented
release or empty-close events.

Completion is one of these exact shapes:

```text
{"kind":"value","type":"i64","value":"42"}
{"kind":"trap","trap":"index_out_of_bounds"}
{"kind":"resource_limit"}
{"kind":"infrastructure","reason":"..."}
```

The value shape above is for the executable `i64` entry. Trap tags include the
existing arithmetic traps plus `invalid_length` and `index_out_of_bounds`.
JSON key order is not semantic. Duplicate keys, noncanonical numbers, unknown
keys/tags and incorrect pairings do not become valid evidence through JSON
normalization.

## Formal reference runner

Build the pinned Lean executable from `formal/`:

```sh
lake build anl_memory_reference_runner
```

It accepts exactly four arguments:

```text
formal/.lake/build/bin/anl_memory_reference_runner CORE_JSON RESPONSE_PLAN_JSON FUEL TRANSITIONS
```

`FUEL` is canonical unsigned decimal in `0..1000000000`; `TRANSITIONS` is
canonical unsigned decimal in `0..262144`. Paths contain 1–4096 UTF-8 bytes.
Core input is bounded to 1 MiB and fully checked even when either budget is zero.
The response plan is separately bounded to 1 MiB and has exactly these fields:

```json
{"schema":"anl-memory-response-plan-v1","responses":["success","refused"],"default":"success"}
```

`responses` contains at most 65,536 `success`/`refused` strings. The mandatory
`default` makes the abstract allocator response stream total: requests beyond
the vector use that response. Unused vector entries are permitted. This protocol
does not assert exact native replay; a comparison must separately validate the
observed trace and whether any default response was used.

The executable invokes the accepted checked entry constructor and `Tool.run`.
Expression entries and successful positive-allocation preflight consume the
expression/fill fuel; administrative transitions consume `TRANSITIONS`.
Transition budget zero tests stopping structurally and does not evaluate a
pending allocation. An exhausted transition budget retains the exact machine,
world and meter prefix. It is visibly incomplete, not a language trap or a
language resource limit.

One JSON line has exactly `schema`, `status`, `semantic_revision`,
`allocation_profile`, `fuel`, `transition_budget`, `resource_reason`, `reason`,
`meter`, and `trace`. The schema is `anl-memory-reference-run-v1`. When available, the input
budgets and meter fields are canonical decimal strings; invalid CLI arguments
leave the budget fields null. The meter reports
`fuel_remaining`, `active_slots`, `live_cells`, `tuple_fields` and
`expression_depth` before bookkeeping unwind.

| Status | Exit | Meaning |
| --- | --- | --- |
| `value` | 0 | Normal checked entry result; trace completion is `value` |
| `trap` | 2 | Defined semantic trap; trace retains all live scopes |
| `resource_limit` | 3 | Interpreter policy boundary with retained prefix |
| `transition_limit` | 5 | Administrative budget exhausted; incomplete prefix |
| `rejected` | 1 | Malformed documents or invalid checked Core input |
| `error` | 4 | Invalid arguments, input/output limits, I/O or other infrastructure failure |

A resource reason is exactly `depth`, `expression_fuel`, `slots`, `live_cells`,
`fill_fuel` or `tuple_fields`. The `reason` repeats that tag. A transition limit
uses reason `administrative transition budget exhausted` and an `infrastructure`
trace completion with that same reason. Value and trap reasons are empty.
Rejected and error reports have null trace; rejection before a checked program
has null profile and meter. An error after execution/export can retain the
profile and meter but still has null trace. Diagnostics are bounded to 1024 UTF-8
bytes. Output, including its final LF, is bounded to 8 MiB, and trace export to
65,536 events. Export failure is infrastructure failure, not a source-level
resource boundary.

The proofs relate every returned semantic prefix to independent Core steps,
bound event growth by the supplied administrative budget, and inherit checked
safety. Encoder bounds apply to the constructed output bytes. Byte parsing,
JSON/ByteArray implementation, I/O and host execution remain trusted boundaries.

## Comparison scope

The [portable corpus](../validation/memory/README.md) lives under
`validation/memory/`. Start with `python3 validation/memory/run.py audit`; its
`gate` command takes explicit ordinary/evidence compiler, exporter, pair checker,
raw probe, reference runner and C compiler paths, plus a fresh results directory.
The primary groups are `static,bridge,pairs,controls`; boundary groups are explicit
additional selections. Its audit checks pinned
fixtures, independent expected results/traces, and runner inputs. Its bridge
includes 24 source-export cases and 29 raw Core cases. The accepted reference
run covered all 53: 18 values, 8 traps, 7 resource limits and 20 rejections.
This is finite empirical evidence in addition to the formal theorems, not a
proof of Rust/native agreement on all programs. Resource-limited prefixes are
not completed native comparisons. Missing reports, host failures, administrative
exhaustion and invalid report formats are incomplete evidence.

See the [trust boundary](../docs/architecture/trust.md),
[proof inventory](../formal/PROOFS.md#owned-buffers-and-coremir-correspondence),
and [native compilation guide](../docs/native-compilation.md).
