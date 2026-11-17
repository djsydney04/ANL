# Native scalar baseline on macOS arm64

Native execution was faster for the branching Fibonacci programs in this run.
The small constant and three-file controls had overlapping timing ranges. This
compares two APL execution modes for four specific programs, with no general
language-performance or cross-language claim.

Compiler source is pinned to `19d726cca188f04229e0962f4d903be3ebf4a9cb`.
The [raw measurements](native-macos-arm64.json) include all 175 recorded
invocations, their commands, outputs and statuses, CPU and wall time, artifact
sizes and hashes, and linked-binary disassembly. No unexpected failure occurred.
The run contains seven samples per operation after one preflight and two warmups,
for 84 measured samples. Round traversal reverses each time.

## Observed latency and size

Wall time is milliseconds, shown as median [minimum, maximum]. Native runs use
already-built executables whose first launch completed before the warmups.
Interpreter runs include process launch, source loading, parsing, checking and
evaluation. Build runs include those frontend steps, C emission, the host C
compiler/linker, and output publication. Build-result execution is validated
separately and excluded from build latency.

| Program | Native build ms | Warmed native run ms | Interpreter CLI ms | Native bytes |
| --- | ---: | ---: | ---: | ---: |
| constant-control | 45.841 [44.515, 54.208] | 2.661 [2.088, 4.730] | 3.535 [2.658, 4.545] | 33656 |
| three-modules | 46.150 [45.462, 48.355] | 2.464 [2.000, 5.097] | 2.767 [2.585, 5.559] | 33656 |
| fibonacci-28 | 46.936 [46.097, 51.217] | 3.252 [2.929, 7.164] | 56.944 [54.737, 60.087] | 33784 |
| fibonacci-32 | 46.317 [44.807, 48.842] | 8.371 [8.088, 9.443] | 363.726 [363.144, 369.076] | 33784 |

The release compiler itself is 867232 bytes. Native executables include the scalar
runtime and host executable metadata, and dynamically link system libraries. File
length is not a memory-use measurement.

Fibonacci(28) returns `317811`; Fibonacci(32) returns `2178309`. A separate iterative
integer calculation supplied these expected results. Both native and interpreter
runs must match them exactly, including newline and exit status. Interpreter fuel
was explicitly set to 1000000000, and neither depth nor fuel was exhausted.

## What performed the work

The actual linked Fibonacci binaries contain a call from `main` to `apl_f0` and
two recursive calls within `apl_f0`. Their complete disassembly and companion
`-O2` assembly are in the raw report. These executions were not constant-folded
into printing the answer. The constant and three-module controls may be folded;
they measure startup and build overhead, not arithmetic throughput.

For Fibonacci(32), median native user/system CPU time was 6.516/0.807 ms, compared
with 8.371 ms wall time. Interpreter user/system time was 361.405/1.021 ms versus
363.726 ms wall time. Computation dominates the larger interpreter case; process
and runtime startup remain a material share of the native case.

Separate one-second macOS `sample` profiles used the identical compiler binary
with larger inputs to make the same recursive computation observable. They are
excluded from all benchmark timings. The native Fibonacci(44) run returned
`701408733`; 582 samples had `apl_f0` at the collapsed top of stack, and 145 were
in `_dyld_start`. The interpreter Fibonacci(36) run returned `14930352`; its
collapsed top frames included 390 samples in `Evaluator::expr`, 74 in scalar
`binary`, and several allocation/free routines. `src/eval.rs` allocates a fresh
argument vector for each function call. These profiles locate recursive execution
and interpreter allocation work; they do not quantify a prospective optimization.

The [compressed profile evidence](native-macos-arm64-profiles.json.gz) retains
source text/hashes, compiler hash, commands, exact outcomes, and complete sampling
output. Decompress it with Python's `gzip` module or `gzip -dc`. To reproduce the
profile inputs, replace only the final `fibonacci(32)` call in the checked-in
fixture with `fibonacci(44)` for native execution or `fibonacci(36)` for the
interpreter, then run `sample PID 1 1 -file profile.txt` during execution. Run these
profiles separately from timing samples.

Newly built executables' initial launches took 108.340–197.300 ms in the four
setup observations. Those observations are retained separately, not discarded or
mixed into warmed results. The cause of the first-launch delay was not isolated;
the profile does show loader activity. No cold-cache or first-use guarantee follows
from the warmed latency table.

## Reproduction and limits

```sh
PATH="$HOME/.cargo/bin:$PATH" python3 -m unittest discover -s benchmarks -p 'test_*.py'
PATH="$HOME/.cargo/bin:$PATH" python3 benchmarks/native.py \
  --revision 19d726cca188f04229e0962f4d903be3ebf4a9cb \
  --warmup 2 --samples 7 --output benchmarks/results/native-local.json
```

The harness builds the release compiler from scratch in a private temporary Cargo
target directory, using `--locked --offline`. Dependencies must already be cached;
that setup is recorded separately from APL program-build timing. The compiler's
source files, Cargo manifest/lockfile, and toolchain file must match the pinned Git
tree. Documentation-only commits may differ. Benchmark sources and the harness
have their own recorded hashes. Inputs, tools and native artifacts are checked
again after sampling. Changed inputs invalidate the result. A failure writes a
rejected partial report with its observed output instead of publishing a success
summary.

The run used Rust 1.99.1, Apple clang 21.0.0, Python 3.9.6, and macOS 26.4.1 on
arm64 with ten logical CPUs. Actual Rust compiler/Cargo, Clang, linker, and launcher
hashes are recorded. The native backend uses `-std=c11 -O2`. No additional native
optimization flags or interpreter implementation tuning were applied.

This was a shared host with unrelated virtualization and indexing activity.
Load averages were about 5.23 at the start and 5.39 at the end. Operations were
interleaved to reduce ordering bias. Cache state was warm and uncontrolled.
Seven samples and one host cannot establish production distributions or platform
comparability. Do not subtract the constant control from other timings or treat
these results as memory, compiler-correctness, C/Rust comparison, or release
qualification evidence.
