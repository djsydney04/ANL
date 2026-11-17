# Initial CLI capability and latency baseline

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
