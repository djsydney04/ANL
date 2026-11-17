# Performance baselines

## Initial interpreter CLI baseline

This harness records the wall-clock time a user waits for `anl check` or
`anl eval`: process launch, source-file reading, parsing, checking, and optional
interpretation. It measures the release CLI, not native generated code. There is
no earlier compiler baseline for that initial experiment and no speedup or cross-language performance
claim.

```sh
cargo build --release --locked
python3 -m unittest discover -s benchmarks -p 'test_*.py'
python3 benchmarks/run.py --warmup 2 --samples 7 --output benchmarks/results/local.json
```

Python 3 and a POSIX host are required. The current default executable is
`target/release/anl`; `--binary` can select the historical `apl` executable when
replaying an older checkout. Historical fixture bytes and recorded results retain
their original names. `--binary` selects another release binary;
`--manifest` selects another explicit case list. The harness refuses fewer than
five samples or one warmup. Each command has a ten-second timeout by default.

The versioned [manifest](cases/manifest.json) supplies independently expected
results, rejection statuses, and trap tags. Before recording measured rounds,
the harness checks every fixture through both CLI operations. Every warmup and
sample is checked again; a wrong value, unexpected rejection, wrong trap, missing
diagnostic, timeout, or crash rejects the run. Expected nonzero statuses are
counted separately. The harness's own tests inject wrong values and trap kinds
to demonstrate that the semantic gate rejects them.

Cases cover recursive factorial, Euclid's algorithm, prime enumeration, branching
Fibonacci recursion, a linear arithmetic recurrence, short-circuiting, a 200-function
module, and expected arithmetic/source failures. Samples alternate traversal
order across cases. The JSON report contains every command's full output, status,
wall/user/system time, warmup and measured samples, median and range, source and
binary hashes, toolchain version, host details, and the revision/worktree state.
Timing `--version` supplies a process-startup control, not a number to subtract
from end-to-end results.

These small inputs are sensitive to process startup, scheduling, and filesystem
cache state. Repeated runs warm the operating-system caches; no cold-cache claim
is made. CPU times are observations, not a profile of compiler internals. A
bottleneck or optimization claim needs a separate profile and representative
larger workloads. Neither this baseline nor passing fixtures establish native
performance, memory efficiency, formal correctness, or full-language capability.

The checked-in result and accompanying notes record the actual local run. CI
checks correctness of the harness but does not impose machine-dependent latency
thresholds.

## Native build and execution baseline

The original native baseline measures `apl build`, warmed generated executables,
and the release interpreter against the same explicit output oracles. It covers
a constant control, the three-file module example, and two branching Fibonacci
inputs. Read the [macOS arm64 result](results/native-macos-arm64.md) for actual
medians/ranges, linked-binary evidence that recursion remains, separate profiles,
first-launch observations, and limitations.

```sh
python3 -m unittest discover -s benchmarks -p 'test_*.py'
python3 benchmarks/native.py --revision 19d726c --warmup 2 --samples 7 \
  --output benchmarks/results/native-local.json
```

These commands describe the original compiler and manifest snapshot. Use the
[local-state command below](#local-state-build-and-execution-baseline) for the
current manifest. The compiler inputs must match the selected Git revision.
The harness builds a fresh isolated release compiler with cached Cargo dependencies, checks source,
fixture, tool and artifact hashes, and validates every observed outcome. Native
build samples use separate outputs from the stable executables used for run
samples. First launches and validation runs remain in the raw evidence but are
not mixed into warmed execution samples. Failed or changed-input runs write a
rejected partial report. The default revision pins this baseline; use
`--revision` to identify a later committed compiler when measuring it.

Measurements are observational results from a shared host. They do not establish
cross-language performance, memory efficiency, or a qualified release.

## Local-state build and execution baseline

The [local-state macOS arm64 report](results/local-state-macos-arm64.md) records
mutable-local and while-loop measurements at exact compiler revision
`f8ffb5f128aab5eaed4db3770ae500cd923cc61c`. It adds a million-step arithmetic
recurrence with an independent expected result, retaining the original four
programs as controls. The separate run records 220 validated invocations and
105 measured samples, with linked-binary evidence that the loop executes.

With compiler inputs matching that revision and Cargo dependencies already
cached, reproduce the current manifest using:

```sh
python3 benchmarks/native.py \
  --revision f8ffb5f128aab5eaed4db3770ae500cd923cc61c \
  --warmup 2 --samples 7 --output benchmarks/results/local-state-local.json
```

The earlier native baseline and its raw evidence remain unchanged. The new
workload, compiler revision, and shared-host conditions do not establish a
before-and-after speedup or a cross-language comparison. Read the report for
workload-specific results, profile evidence, first-launch exclusions, and limits.

## Contract verification coverage and latency

The [loop-free state verification report](results/verification-macos-arm64.md)
compares pure-program outcomes and records new mutable-state proof coverage at
`5e9dff071bf58a369af0386fb042c5948dcf8862`. Its 100 measured samples keep verified,
failed, unknown and unsupported outcomes separate. Pure timing ranges overlap;
old state rejection costs are not compared with successful proof costs.

The report links exact raw data, the original measured script and profile,
and build/reproduction instructions for [verification.py](verification.py).
The configurable harness checks complete reports, exact hashes, independent
finite outcomes, and four deliberate failures of its own semantic gate before
timing, including a missing SAT model.
Use `--gate-only` to run just those checks. It requires explicit baseline,
candidate and solver paths; the earlier runtime baselines remain unchanged.

## Invariant-loop verification coverage and latency

The [invariant-loop report](results/loop-verification-macos-arm64.md) compares
`0795dd689c40b88d0a0ae37e25bfdc3b06468f8e` with
`14bb053ca5e09f6036e1a61089452f8ccf90d375`: four shared pure/state controls,
eight loop cases and one bounded symbolic-work failure. Five samples per side
show overlapping shared-workload ranges; no speedup or regression is established.
Old unsupported-loop latency measures rejection, not proof cost.

The self-contained [loop harness](loop_verification.py) and
[13-case manifest](cases/loop-verification/manifest.json) retain exact report,
SMT, model, source/tool identity and runtime gates. The report includes commands
for `gate` and `time`, deliberate new-host identity recording, unchanged original
raw evidence, a source/harness snapshot, and limits of the loaded-host results.

## Flat-product representation measurements

The [ANL flat-product report](results/flat-products-macos-arm64.md) retains all
ten official paired runs at the pre-rename semantic checkpoint, including
scalar review flags and the retained-singleton memory cost. Its
[self-contained controller](flat_products.py) checks frozen inputs, source/tool
identities, outputs, exported bytes and native sizes. Historical reproduction
commands use the `apl` executables built from the recorded commits; these results
do not identify the later renamed `anl` binary.


## Tuple-verification coverage and latency

The [ANL tuple-verification report](results/product-verification-macos-arm64.md)
records 351 validated processes: paired scalar comparisons and absolute costs
for 15 newly supported tuple workloads. Five resource-limit outcomes and one
expected evaluation trap remain in the mandatory 33-case semantic gate.
Background host activity, all timing ranges and the 40-to-64-byte internal
representation limitation remain explicit; performance attribution is
inconclusive.

The standalone [runner](product_verification.py) audits the exact archived
observations without invoking a compiler. Its `gate` and `time` commands accept
explicit compiler, solver and source paths, validate pinned source inputs and
record new host identities. The report includes build/replay commands and the
complete raw measurement and preflight archives.
