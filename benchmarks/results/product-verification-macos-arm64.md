# ANL tuple-verification measurements

One macOS arm64 run records the end-to-end cost of contract verification with
flat tuples. All 351 compiler processes passed their acceptance checks: 78
warmups and 273 measured samples, comprising 84 scalar pairs and 105
candidate-only tuple samples. Performance attribution remains inconclusive.

The baseline is `5fd9bf85708c38056b26751035df843dfe88a303`; the candidate source is
`274e9afad46412e9087a11b58b983d7a2c061098`. The measured candidate was built from
those exact compiler inputs before the commit was created. The
[source and tool record](product-verification-sources.json) binds each commit's
21 compiler/configuration inputs, release binary, build flags, Rust 1.99.1,
Z3 5.3.3, Python version, and build environment. The separate 45-file source
digest covers a broader compiler, test and example inventory; it is not the 21-input compiler
digest. Source/build correspondence is an attestation, not a proof of compiler
correctness.

## Scalar comparisons

Each case has two warmup pairs and seven measured pairs. Across cases, the
measured schedule contains 42 baseline-first and 42 candidate-first pairs.
Wall values below are milliseconds, with the full observed range in brackets.
Ratios are medians of the seven matched candidate/baseline ratios, not ratios
of independent side medians. The [numeric summary](product-verification-macos-arm64-summary.json)
also retains CPU/RSS medians, every range, every paired ratio and work counters.

| Case | Baseline wall median [min, max] | Candidate wall median [min, max] | Paired wall C/B | Paired CPU C/B | Paired RSS C/B |
| --- | ---: | ---: | ---: | ---: | ---: |
| scalar-bindings-16 | 214.126 [211.653, 252.028] | 214.483 [213.665, 216.587] | 1.00148 | 1.00512 | 1.00000 |
| scalar-bindings-2 | 194.162 [192.353, 196.330] | 194.537 [192.454, 209.514] | 1.00415 | 1.00438 | 1.00000 |
| scalar-bindings-8 | 201.428 [198.815, 203.767] | 202.546 [200.141, 226.958] | 1.01351 | 1.00089 | 1.00000 |
| scalar-calls-16 | 573.873 [558.140, 647.204] | 570.445 [561.506, 719.408] | 1.00423 | 1.01047 | 1.00000 |
| scalar-calls-2 | 254.974 [246.699, 263.173] | 254.086 [251.393, 260.490] | 0.99652 | 1.00052 | 1.00000 |
| scalar-calls-8 | 370.925 [365.498, 377.256] | 373.512 [366.859, 401.180] | 1.00358 | 1.00067 | 1.00000 |
| scalar-loop | 179.982 [174.910, 183.328] | 177.815 [174.059, 188.267] | 0.99513 | 1.00428 | 1.00000 |
| scalar-loops-16 | 552.415 [549.125, 580.024] | 555.292 [544.431, 562.057] | 1.00018 | 1.00376 | 1.00000 |
| scalar-loops-2 | 194.708 [191.171, 203.354] | 194.097 [191.888, 195.464] | 0.99293 | 1.00168 | 1.00000 |
| scalar-loops-8 | 326.508 [319.840, 332.384] | 325.710 [323.830, 326.469] | 0.99832 | 0.99834 | 1.00000 |
| scalar-pure | 195.613 [193.283, 198.341] | 195.305 [193.701, 197.542] | 0.99793 | 1.00641 | 1.00000 |
| scalar-state | 157.076 [154.762, 158.813] | 157.032 [155.993, 159.422] | 1.00064 | 1.00189 | 0.99950 |

Paired median wall changes ranged from −0.71% to +1.35%; CPU changes ranged
from −0.17% to +1.05%. No case crossed the predefined investigation thresholds
of 10% for wall/CPU or 15% for RSS. These thresholds identify cases to
investigate; passing them establishes neither a speedup nor general absence of
regressions.

## Absolute tuple-verification costs

These 15 cases have two warmups and seven measured samples each. The baseline
does not support their proof obligations, so its rejection latency is not a
proof-cost comparison. Widths 1, 2 and 8 include scalar and mixed tuple fields;
`unit8` contains eight unit fields. Copy/call and loop families vary their
binding/site count. Exact programs and independently specified runtime values
are in the [33-case manifest](../cases/product-verification/manifest.json).

| Case | Wall ms median [min, max] | CPU ms median [min, max] | RSS MiB median [min, max] |
| --- | ---: | ---: | ---: |
| product-copy-calls-unit8-2 | 203.809 [199.456, 205.134] | 171.978 [171.249, 172.992] | 31.375 [31.359, 31.406] |
| product-copy-calls-unit8-8 | 222.705 [219.075, 226.427] | 192.832 [192.076, 196.058] | 33.156 [33.141, 33.172] |
| product-copy-calls-w1-2 | 204.781 [203.018, 218.628] | 171.985 [171.728, 175.852] | 32.578 [32.562, 32.578] |
| product-copy-calls-w1-8 | 208.727 [206.103, 218.039] | 178.170 [177.676, 182.060] | 32.875 [32.859, 32.906] |
| product-copy-calls-w2-2 | 204.792 [203.529, 221.146] | 172.583 [171.605, 187.143] | 32.562 [32.562, 32.578] |
| product-copy-calls-w2-8 | 283.200 [282.103, 287.081] | 254.320 [252.573, 256.125] | 33.016 [33.000, 33.031] |
| product-copy-calls-w8-2 | 207.965 [206.012, 211.713] | 176.396 [175.501, 179.646] | 34.203 [34.188, 34.219] |
| product-copy-calls-w8-8 | 363.268 [348.727, 378.533] | 330.434 [317.875, 347.532] | 34.203 [34.203, 34.219] |
| product-identity-w1 | 183.886 [179.600, 190.311] | 158.706 [157.939, 164.217] | 32.578 [32.562, 32.578] |
| product-identity-w2 | 183.121 [182.201, 311.538] | 158.732 [158.152, 219.727] | 32.578 [32.562, 32.578] |
| product-identity-w8 | 185.031 [181.705, 206.634] | 159.877 [158.768, 166.268] | 34.188 [34.188, 34.219] |
| product-loops-unit8-2 | 214.855 [198.298, 233.362] | 184.245 [173.523, 194.343] | 31.625 [31.594, 31.625] |
| product-loops-w1-2 | 196.675 [195.493, 198.128] | 168.563 [167.456, 169.992] | 32.359 [32.359, 32.391] |
| product-loops-w2-2 | 197.922 [195.918, 199.934] | 170.297 [169.438, 171.909] | 32.531 [32.531, 32.562] |
| product-loops-w8-2 | 216.778 [205.670, 238.955] | 183.030 [178.062, 188.926] | 32.891 [32.891, 32.906] |

The identity-width-2 sample at 311.538 ms is retained beside its 183.121 ms
median. No outliers or warmups were removed from the evidence.

## Resource outcomes and correctness gate

All 33 final preflight cases passed their expected outcomes: 12 scalar cases,
15 verified tuple cases, five `unknown` resource outcomes, and one expected
full-field evaluation trap. Each case also checks interpreter behavior, typed
core evaluation, and exact core bytes against its annotation-free counterpart.
Scalar reports match between compiler versions after explicit compiler identity
and remaining-time normalization; raw query digests are checked first.
Every timed report then matches its preflight report, including work counters,
SMT queries, model metadata, proof scope and status.

Four larger loop cases initially expected `verified` but returned `unknown` at
the fixed one-million-unit symbolic-work limit. Their original sources and
initial expectations are retained, along with the failed preflight. Before
timing, they were reclassified as resource observations and rerun; no source
was shrunk and no runtime expectation changed. An 80-postcondition case is
the fifth resource observation. All five remain mandatory in the final gate
and are excluded from throughput statistics.

The manifest retains the original `AMENDMENT-v2.md` label as provenance. This
report supplies its technical rationale; the runner does not resolve that label.

| Resource case | Completed queries | Symbolic work | Completed query bytes |
| --- | ---: | ---: | ---: |
| product-loops-w1-8 | 10 | 999992 | 938957 |
| product-loops-w2-8 | 6 | 999963 | 819735 |
| product-loops-w8-8 | 2 | 999987 | 608133 |
| product-loops-unit8-8 | 3 | 999980 | 812511 |
| product-render-work-limit | 18 | 999858 | 976713 |

The earlier two preflight stages used candidate binary `7c2004a997a813b…`;
the final complete gate and all timed samples used `50a16061f0acbb4c…`.
Each stage retains its original binary identity and report scope. The final
[proof scope](../cases/product-verification/scope.json) describes partial
correctness of the modeled fragment with SMT trust. Rust generation, source
annotation correspondence, SMT encoding/answers, native execution, termination,
and generation completeness under production budgets remain explicit gaps.
Neither the gate nor these timings closes those gaps.

## Host and measurement limits

The host ran macOS 26.4.1 on arm64 with ten logical CPUs. It was on AC power,
with no thermal or performance warning recorded. Boundary load averages were
4.61 and 5.50. A Virtualization process showed 316.5% and 319.0% CPU in the
two snapshots, with other background activity also retained. These snapshots
establish host activity, not its cause or contribution to any particular
sample. No limiter profile or separate investigation run was performed.

Wall time spans process launch through `wait4` return. CPU is the reaped
process's user plus system accounting; a separate synthetic fixture confirmed
inclusion of one synchronously waited child on this host. It does not validate
arbitrary unwaited or escaped descendants. RSS is the kernel high-water value,
in native macOS bytes, not simultaneous summed compiler/solver tree memory.

The 2/8/16 scalar families and high-water RSS cannot isolate or rule out the
internal Cell/Flow size increase from 40 to 64 bytes. Similar RSS readings do
not establish unchanged allocation or copying costs. These observations do
not identify a bottleneck, attribute variation to background load, or establish
native-code or cross-language performance.

## Evidence

- [Measurements archive](product-verification-macos-arm64.json.gz): all 351 exact
  command records, stdout/stderr, raw SMT queries and digests, statuses, work
  counters, wall/CPU/RSS observations, samples, original summary and environment
  snapshots. Historical absolute paths remain literal observations; they are
  not dependencies of the replay tool.
- [Preflight archive](product-verification-gates.json.gz): the original failed
  stage, four-case resource amendment, complete final gate, runtime/core outputs
  and technical identities. [Initial expectations](product-verification-initial-expectations.json)
  retain the original classification.
- [Technical experiment record](product-verification-experiment.json),
  [accounting evidence](product-verification-accounting.json) and
  [artifact index](product-verification-artifacts.json): configuration,
  timing primitive, thresholds and SHA-256 inventories. Technical metadata was
  extracted from the original experiment; its original digest is retained.
  The numeric summary preserves all numerical analysis fields and records the
  original analysis digest; only descriptive metadata was edited.

Both archives are deterministic gzip files containing JSON with a `files`
mapping. Each entry holds its exact UTF-8 `text` and `sha256`. Re-encoding that
text as UTF-8 recovers the original bytes. The offline audit checks every
archive entry, all sample report/query hashes, the complete schedule, the
final semantic gate and summary calculations. It launches no compiler or
solver. Raw reports include local paths as provenance; copying those paths
into a new command is unnecessary.

## Reproduce

Python 3.9 or later and a POSIX host with `wait4` are required. The runner uses
only Python's standard library. macOS and Linux RSS units are recorded
explicitly. First audit the packaged observations:

```sh
python3 benchmarks/product_verification.py audit
```

Build the exact compiler commits in separate checkouts with Rust 1.99.1 and
`cargo build --locked --release`. Keep their release binaries separate. For
example, from a checkout containing this benchmark package:

```sh
git worktree add --detach ../anl-benchmark-baseline 5fd9bf85708c38056b26751035df843dfe88a303
git worktree add --detach ../anl-benchmark-candidate 274e9afad46412e9087a11b58b983d7a2c061098
(cd ../anl-benchmark-baseline && cargo +1.99.1 build --locked --release)
(cd ../anl-benchmark-candidate && cargo +1.99.1 build --locked --release)
```

Use a Z3 5.3.3 executable. The source/tool record lists the original build
environment and executable hashes; a new platform or build may produce
different executable hashes. The following records those explicitly as a new
measurement identity while requiring the same compiler source inputs and tool
versions. Set the solver path and choose a fresh output directory:

```sh
ANL_BASE_SOURCE="$(cd ../anl-benchmark-baseline && pwd)"
ANL_CAND_SOURCE="$(cd ../anl-benchmark-candidate && pwd)"
ANL_BASE="$ANL_BASE_SOURCE/target/release/anl"
ANL_CAND="$ANL_CAND_SOURCE/target/release/anl"
ANL_SOLVER=/absolute/path/to/z3-5.3.3
ANL_OUT="$PWD/benchmark-local/product-verification"
ANL_RUSTC="$(rustup which --toolchain 1.99.1 rustc)"
ANL_CARGO="$(rustup which --toolchain 1.99.1 cargo)"

run_product_benchmark() {
  python3 benchmarks/product_verification.py "$1" \
    --baseline "$ANL_BASE" --candidate "$ANL_CAND" --solver "$ANL_SOLVER" \
    --baseline-source "$ANL_BASE_SOURCE" --candidate-source "$ANL_CAND_SOURCE" \
    --rustc "$ANL_RUSTC" --cargo "$ANL_CARGO" --out "$ANL_OUT" \
    --new-host \
    --baseline-sha256 "$(shasum -a 256 "$ANL_BASE" | awk '{print $1}')" \
    --candidate-sha256 "$(shasum -a 256 "$ANL_CAND" | awk '{print $1}')" \
    --solver-sha256 "$(shasum -a 256 "$ANL_SOLVER" | awk '{print $1}')"
}
run_product_benchmark gate
run_product_benchmark time
```

`gate` records new tool, source and host identities, validates waited-child CPU
accounting, and checks all 33 cases. `time` requires that successful unchanged
gate and runs the fixed 351-process schedule. Each mode retains raw outputs;
timeouts, unexpected statuses, changed sources/tools, report differences and
typed-value mismatches reject the run. Context and identity checks are outside
the timed interval. The runner neither builds compilers nor changes the corpus.
For replay with the original executable hashes, omit `--new-host` and the three
hash arguments. New results stay in the chosen output directory and do not
replace the historical archives.
