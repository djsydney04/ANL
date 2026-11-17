# Performance baselines

## Initial interpreter CLI baseline

This harness records the wall-clock time a user waits for `apl check` or
`apl eval`: process launch, source-file reading, parsing, checking, and optional
interpretation. It measures the release CLI, not native generated code. There is
no earlier APL compiler baseline and no speedup or cross-language performance
claim.

```sh
cargo build --release --locked
python3 -m unittest discover -s benchmarks -p 'test_*.py'
python3 benchmarks/run.py --warmup 2 --samples 7 --output benchmarks/results/local.json
```

Python 3 and a POSIX host are required. `--binary` selects another release binary;
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

The native harness measures `apl build`, warmed generated executables, and the
release interpreter against the same explicit output oracles. It covers a
constant control, the three-file module example, and two branching Fibonacci
inputs. Read the [macOS arm64 result](results/native-macos-arm64.md) for actual
medians/ranges, linked-binary evidence that recursion remains, separate profiles,
first-launch observations, and limitations.

```sh
python3 -m unittest discover -s benchmarks -p 'test_*.py'
python3 benchmarks/native.py --revision 19d726c --warmup 2 --samples 7 \
  --output benchmarks/results/native-local.json
```

The compiler inputs must match the selected Git revision. The harness builds a
fresh isolated release compiler with cached Cargo dependencies, checks source,
fixture, tool and artifact hashes, and validates every observed outcome. Native
build samples use separate outputs from the stable executables used for run
samples. First launches and validation runs remain in the raw evidence but are
not mixed into warmed execution samples. Failed or changed-input runs write a
rejected partial report. The default revision pins this baseline; use
`--revision` to identify a later committed compiler when measuring it.

Measurements are observational results from a shared host. They do not establish
cross-language performance, memory efficiency, or a qualified release.
