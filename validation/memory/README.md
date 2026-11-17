# Memory validation

This corpus checks the owned-buffer source, Core, MIR, native runtime, and bounded
reference interfaces. It keeps expected results and traces as reviewed input
files. It never asks the compiler under test to generate an expected answer.

Run the offline fixture/integrity check from any working directory:

```sh
python3 validation/memory/run.py audit
```

Run the main bridge with explicit executable paths and a fresh output directory:

```sh
python3 validation/memory/run.py gate \
  --groups static,bridge,pairs,controls \
  --rust /absolute/path/to/anl-default \
  --evidence /absolute/path/to/anl-evidence \
  --exporter /absolute/path/to/memory_evidence \
  --pair /absolute/path/to/anl_memory_pair_checker \
  --raw /absolute/path/to/anl_memory_raw_probe \
  --reference /absolute/path/to/anl_memory_reference_runner \
  --cc /absolute/path/to/cc \
  --out /absolute/path/to/new-memory-results
```

The default Rust CLI and the feature-enabled CLI must come from the same source
revision. Build the latter with Cargo's `memory-evidence` feature, including its
`memory_evidence` example exporter. The pair, raw, and reference executables come
from the matching formal source revision. Supply a C11 compiler. The fixture
source profile is 64-bit size/ptrdiff, 8-bit bytes and 8-byte i64 alignment; the
source/native groups target hosts with that profile, including qualified 64-bit
Linux and macOS configurations. Raw Core's recorded 32-bit profile is deliberately
kept as recorded and is never converted to host-native execution.

The runner records executable paths, hashes, sizes, Python identity and host
identity. It retains each actual command, raw stdout/stderr, status, capture
limits, input and native-source evidence. It starts no build system or dependency
installer. Run build and proof qualification separately for the selected tools.
A missing required tool is an error; supplying a tool is not evidence that the
matching source/proofs were built correctly.

## Groups and their claims

| Group | Checks actually selected |
|---|---|
| static | 18 source/type/entry cases on both default and evidence CLIs; three unsupported-memory verification cases on both CLIs, with a compiler/solver startup sentinel. |
| bridge | All 24 source and 29 raw Core cases against the bounded reference driver; 33 exact traces and 20 invalid-Core rejections; seven exact resource reasons with matching evaluator diagnostics; evidence source/Core evaluation; ordinary comparisons where the original oracle does not require injected allocation refusal; actual source/exported Core/MIR acceptance; the original completed native routes with captured C/runtime/header bindings. |
| pairs | Three separate raw-validity judgments plus nine canonical/noncanonical pair cases. In particular, rejection of two noncanonical pairs is accompanied by actual raw typing acceptance for their exact Core/MIR bytes. Pair rejection alone is not counted as raw typing evidence. |
| controls | Default-build evidence controls stay ignored; feature-enabled nonexecuting commands and scalar/tuple evaluation stay ordinary; invalid activation/replay refuses before execution/compiler startup; captured native replay remains immutable; exclusive trace creation, repeated execution and record-only behavior retain the original expectations. |
| bounds | Eight at/one-over Core-byte, MIR-byte, replay-byte and replay-event inputs. Inputs are deterministically generated to independently fixed hashes; the event-input checks use fuel0. |
| output-bounds | Two separately selected programs at/over 65536 output events, through evidence evaluation and native execution. Their original full traces are stored as gzip files with exact uncompressed hashes. This group is outside the 53-row reference budget. |

The default group selection is `static,bridge,pairs,controls`. The `controls`
group uses `--rust`, `--evidence`, `--exporter`, `--pair`, and `--cc`; it needs
no baseline compiler or archived result directory. Its scalar/tuple controls
compare the feature-enabled compiler against independent values.

Use `--groups bounds` with `--evidence`, `--pair`, and `--out` to select the input
bounds alone. Use `--groups output-bounds` with `--rust`, `--evidence`, `--exporter`,
`--pair`, `--cc`, and `--out` for output events. The raw tool is required only for
`pairs`; the reference tool is required only for `bridge`. Groups not selected
are not reported as executed or passed.

The 53 bridge rows have fixed outcomes: 18 values, 8 traps, 7 tool resource limits,
and 20 rejected Core artifacts. Each reference call uses its original fuel and
262144 administrative transitions. The reader's byte and structural limits and
runtime depth/slot/cell/tuple policy are unchanged. An administrative cutoff,
missing report, host failure, malformed output, or timeout is incomplete evidence,
not an ANL trap or successful resource-limit match. Every command has bounded
capture and containment. The runner does not measure performance.

A source case is checked, exported through the actual default `dump-core`, and
compared with its accepted retained Core bytes. The evidence exporter then retains
its actual Core, MIR, generated C, runtime C, and header. The pair checker receives
those exact Core/MIR files. Their independently expected traces and outcomes stay
separate from the exported artifacts.

The evidence evaluator and reference driver use the same sealed allocator
responses. Every completed trace is checked in full, including request/empty
identities, sites, lengths, responses, order, cleanup, and completion. Three
response entries may remain unused when an earlier resource preflight stops.
The slots-pending-view root owner is empty: one descriptor and zero cells.
Unused entries do not turn the plan into a failed exact native replay; the
reference plan and the native replay are different interfaces. The accepted
53-row corpus makes no observation of default-plan fallback. The scalar embedding
row follows the ordinary scalar evaluator path and deliberately emits no memory
trace; its reference trace must be empty and its value remains42.

Native execution is limited to the original 18 source rows marked for native
comparison. Resource-only rows and the other sealed interpreter/resource-boundary
fixtures never run natively, even if a particular row has a completed tool result.
Raw Core rows never run natively. For native routes, the pass-through CC adapter
captures actual C/header/object inputs and preserves compiler arguments. Program
and runtime must compile separately without LTO. Their program/runtime/header
bytes must match the actual exported default bundle. Evidence configuration is
retained separately and cannot be passed off as the default runtime. The six
original ordinary source cases also compare default native behavior. The captured
result lists every actual native route and every native exclusion explicitly.

## Failure and scope

Output goes to a new directory outside this package. A failure stops later work;
the runner preserves completed and partial captures and returns nonzero. It never
retries, increases a budget, edits an expectation, or silently excludes a failed
case. The original package and tool hashes are checked again after the run. A
rerun is a new explicitly requested invocation with a new result directory.

These are finite artifact comparisons through trusted compiler/executable,
parser, runtime, host allocation, file/process I/O, and capture boundaries. They
are not a native machine-code proof, equal Core/MIR fuel or step-count claim,
termination proof, full-language release, or complete OS qualification.

Separate historical checks covered ABI-negative builds, output/source alias
protection, post-link publication races, and host filename/path limitations,
including the native non-UTF8 filename case.
This portable runner does not silently claim to repeat them. Serialized
trace-byte exhaustion remains unqualified. The two output-event programs do not
establish that every earlier output-byte guard can be reached. A host failure
creating a long path is not successful coverage of ANL's path bound.

The hosted C allocation runtime is bootstrap compiler support. It is not an
ANL-authored OS memory manager. The entire intended OS still must be authored in
ANL; this corpus does not supply hardware intrinsics, boot code, interrupt or
concurrency safety, a freestanding runtime, or a bootable OS.
