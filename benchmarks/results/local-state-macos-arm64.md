# Local-state baseline on macOS arm64

The million-step local-state program completed in a median 5.615 ms as a warmed
native process and 53.422 ms through the interpreter CLI on this host. Its native
loop remains in the linked executable. This establishes a baseline for mutable
locals and loops at compiler revision
`f8ffb5f128aab5eaed4db3770ae500cd923cc61c`.

The [raw measurements](local-state-macos-arm64.json) contain 220 recorded
invocations with their commands, outputs, statuses, wall and CPU times, hashes,
and assembly evidence. Every observed outcome passed its semantic check. The run
has seven samples per operation after one preflight and two warmups, for 105
measured samples. Traversal order reverses each round.

The original four programs remain as context and controls. Their
[earlier baseline](native-macos-arm64.md) remains unchanged. These runs do not
establish a before-and-after speedup: the compiler revision and host conditions
differ, and the local-state workload is new. Comparing a loop algorithm with
recursive Fibonacci would not establish a compiler optimization either.

## Observed latency and size

Wall time is milliseconds, shown as median [minimum, maximum]. Native runs use
already-built executables after their first launches. Interpreter runs include
process startup, source loading, parsing, checking, and evaluation. Builds include
the frontend, C emission, the host C compiler and linker, and output publication.
Build-result execution is checked separately and excluded from build latency.

| Program | Native build ms | Warmed native run ms | Interpreter CLI ms | Native bytes |
| --- | ---: | ---: | ---: | ---: |
| constant-control | 46.115 [44.900, 52.785] | 3.742 [2.011, 4.476] | 2.865 [2.315, 6.107] | 33656 |
| three-modules | 45.892 [44.162, 58.067] | 2.408 [1.944, 4.787] | 2.861 [2.431, 5.093] | 33656 |
| fibonacci-28 | 46.500 [44.967, 53.261] | 3.282 [3.116, 6.950] | 56.636 [55.487, 60.416] | 33784 |
| fibonacci-32 | 46.760 [45.697, 50.319] | 8.544 [7.318, 9.168] | 368.806 [361.442, 508.167] | 33784 |
| local-state-park-miller-1m | 46.964 [45.701, 49.040] | 5.615 [5.576, 5.833] | 53.422 [52.612, 54.642] | 33656 |

The release compiler is 1078528 bytes. File length includes executable metadata
and is not a memory-use measurement.

## Workload and independent expected result

The [local-state fixture](../cases/local-state-park-miller-1m.apl) starts with
`x = 1` and performs exactly 1000000 updates of
`x = (x * 48271) % 2147483647`. Python modular exponentiation supplies the
independent expected result, rather than reproducing the tested loop:

```python
from math import gcd

assert gcd(48271, 2147483647) == 1
assert pow(48271, 1000000, 2147483647) == 1263606197
assert (2147483647 - 1) * 48271 == 103661183076066
assert 103661183076066 < 2**63 - 1
```

Each remainder keeps the state between zero and the positive modulus. The
coprime multiplier and nonzero seed keep the state nonzero. The largest possible
product is within `i64`, and the counter only reaches one million. Both execution
modes must print `1263606197` followed by a newline and exit successfully.
Interpreter fuel is explicitly set to 1000000000; no resource limit was reached.

## Evidence that the loop executes

The exact timed native binary initializes its counter to 1000000, multiplies the
state at `0x100000498`, reduces it modulo 2147483647, decrements the counter, and
branches back from `0x1000004b8`. After the loop, the final state is passed to
`printf`. The raw report retains that linked-binary disassembly and the companion
`-O2` assembly. The computation was not replaced with a constant answer.

For the million-step case, median native user and system CPU times were 3.887 and
0.776 ms, compared with 5.615 ms wall time. Interpreter user and system times were
51.408 and 0.888 ms, compared with 53.422 ms wall time. The constant and module
controls have overlapping ranges and may be constant-folded. They expose startup
and build overhead; their timings are not subtracted from the loop measurements.

Separate one-second macOS `sample` profiles used larger versions of the same
loop, outside all timing samples. A fresh build from a hash-verified copy of the
accepted compiler sources produced the same compiler binary hash as the timed
run. Native execution used 1000000000 steps and returned `950006538`; interpreter
execution used 40000000 steps and returned `661924541`. Both outputs matched
independent modular exponentiation.

The native profile had 614 collapsed top-of-stack samples in `main`, where the
generated arithmetic loop runs, and 113 in `_dyld_start`. The interpreter profile
had 675 in `Evaluator::expr` and 103 in scalar `binary`, both in `src/eval.rs`.
These observations locate computation in the serial native recurrence and the
interpreter's expression dispatch and arithmetic. They do not quantify a future
optimization or establish processor throughput. Startup remains material for
the million-step native case.

The [compressed profile evidence](local-state-macos-arm64-profiles.json.gz)
contains the capture script, source text and hashes, compiler and executable
hashes, commands, exact outcomes, and complete sampling output. To repeat the
profiles, change only the final `park_miller(1000000)` call to the counts above,
build the native variant, and run `sample PID 1 1 -file profile.txt` during each
execution. The interpreter profile also uses `--fuel 1000000000`. Keep profiling
separate from timing samples.

The five initial native launches took 112.684 to 251.728 ms. Those setup
observations remain in the raw report and are excluded from warmed samples.
The cause of their delay was not isolated; the native profile also observed
loader activity.

## Reproduction and limits

```sh
PATH="$HOME/.cargo/bin:$PATH" python3 -m unittest discover -s benchmarks -p 'test_*.py'
PATH="$HOME/.cargo/bin:$PATH" python3 benchmarks/native.py \
  --revision f8ffb5f128aab5eaed4db3770ae500cd923cc61c \
  --warmup 2 --samples 7 --output benchmarks/results/local-state-local.json
```

The compiler inputs must match the selected revision. The harness builds an
isolated release compiler with `--locked --offline`, so Cargo dependencies must
already be cached. The benchmark manifest and harness have separately recorded
hashes. A manifest case with `inspect: true` requests linked-binary disassembly
and companion assembly; the existing Fibonacci cases also retain that evidence.
Compiler inputs, fixture inputs, tool executables, and warmed artifacts passed
their before-and-after hash checks. The selected revision was also HEAD at both
ends of this run. The five benchmark harness tests passed before measurement.

The run used Rust and Cargo 1.99.1, Apple clang 21.0.0, Python 3.9.6, and macOS
26.4.1 on arm64 with ten logical CPUs. The native backend used `-std=c11 -O2`.
The raw report records actual compiler, Cargo, launcher, C compiler, and linker
paths and hashes.

This was a shared host. Its one-minute load average rose from 5.11 to 5.43; the
initial five-minute average was 16.56. Before the run, unrelated virtualization
used about 322% CPU, with other activity also present. The samples were
interleaved, but scheduling and warm filesystem caches remained uncontrolled.
Seven samples on one host do not establish production distributions, cold-cache
latency, cross-language performance, memory efficiency, formal correctness, or
release qualification.
