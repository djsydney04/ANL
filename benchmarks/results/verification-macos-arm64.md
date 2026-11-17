# Loop-free state verification baseline

The state verifier proves three valid mutation workloads that the previous
verifier rejects as unsupported. It also detects intermediate overflow and stops
an oversized symbolic analysis with `unknown`. The pure-program timing ranges
overlap in this small shared-host run; no performance improvement or regression
is established.

The baseline compiler inputs are from
`f8ffb5f128aab5eaed4db3770ae500cd923cc61c`. The candidate inputs are from
`5e9dff071bf58a369af0386fb042c5948dcf8862`. Both are release binaries. The solver
is Z3 5.3.3. The [unchanged raw result](verification-macos-arm64.json.gz) contains
all 140 verifier invocations and 64 independent evaluator checks. It has SHA-256
`fd6bc4a4b14adee6869a948c04251e4058a7a0ba913e16cded896b5fb9560487`.
The [run snapshot](verification-macos-arm64-snapshot.json.gz) retains the exact
measured script, workload bytes and separate profile, with per-file hashes.

## Outcomes and timings

Each binary/workload pair had one semantic preflight, one warmup and five timed
samples. Binary order alternated within each pair, and workload order reversed
each round. All 204 invocations matched their expected outcome. The 100 timed
samples contain no unexpected failures or excluded outliers.

Times are whole-CLI wall time in milliseconds, reported as median [minimum,
maximum]. They include process startup, source loading/checking, compiler and
solver identity hashes, solver subprocesses, and JSON reporting. Filesystem
caches are warm. A failed contract, exhausted analysis, or unsupported program
is not a successful proof.

| Pure workload | Outcome on both | Baseline ms | Candidate ms | Queries | Visits |
| --- | --- | --- | --- | ---: | ---: |
| Affine arithmetic | verified | 167.577 [166.314, 169.715] | 167.051 [166.013, 167.351] | 4 | 20 |
| Acyclic affine calls | verified | 243.743 [241.476, 256.091] | 244.780 [241.760, 254.451] | 12 | 146 |
| Guarded signed division | verified | 167.014 [164.510, 168.311] | 166.866 [164.747, 168.084] | 4 | 33 |
| False postcondition | failed | 155.625 [154.968, 157.478] | 155.015 [154.570, 156.210] | 3 | 6 |

The pure reports and query text agree after normalizing actual compiler identity,
remaining timeout values, derived query hashes, and descriptive proof-scope prose.
The false postcondition is an expected solver refutation. It is kept separate
from the three verified cases.

| State workload | Candidate outcome | Candidate ms | Queries | Query bytes | Visits |
| --- | --- | --- | ---: | ---: | ---: |
| Scope exit and assignment RHS effects | verified | 176.139 [174.738, 177.998] | 5 | 22926 | 46 |
| Conditional state and immutable snapshot | verified | 169.577 [167.361, 174.774] | 4 | 21997 | 57 |
| Ordered argument snapshots and callee state | verified | 210.350 [206.939, 211.842] | 8 | 51952 | 132 |
| Intermediate overflow | failed | 146.121 [144.605, 148.573] | 2 | 2841 | 13 |
| Attempt-wide symbolic work ceiling | unknown | 203.184 [201.113, 205.307] | 2 | 295962 | 4589 |
| Statically false while loop | unsupported | 2.560 [2.334, 2.639] | 0 | 0 | 0 |

The old verifier reports `unsupported` for all six state cases. Its rejection
medians are 3.002, 3.185, 3.202, 3.069, 18.042 and 2.534 ms respectively; their
ranges remain in the raw result. These rejection costs are not before-and-after
proof timings. The larger work-ceiling input also takes longer to load and check.

The work-ceiling fixture has 4000 unit parameters, 70 branches that leave most
cells unchanged, and a caller that expands the leaf again. It retains the leaf's
two completed queries before returning `unknown` for the shared symbolic-work
budget. It does not verify the caller. The loop case confirms that invariants
and loop verification remain unsupported.

The finite oracles independently check `3*x+7`, nested affine composition
`4*x+18`, signed truncating division, retained outer-cell updates, branch snapshots,
and the argument-order relation `12202*x+22505`. The overflow workload is also
executed and must trap. These examples supplement the verifier tests; they do
not prove generator correctness.

## Host and profile limits

The host was macOS Darwin 25.4.0 on arm64 with 10 logical CPUs. One-minute load
was 5.267 at the start and 5.287 at the end. An unrelated virtual machine consumed
about 313–320% CPU. Five samples and overlapping ranges do not support a small
speedup claim, and the corpus does not represent large verified applications.

A separate untimed profile verified 80 copies of the branch function, completing
320 obligations and 4560 expression visits. The parent process had 793 sampled
stacks; 791 were in `Solver.query`. Of 500 stacks in its polling path, 499 were
in sleep, and 210 further stacks were in sleep beneath process completion.
This shows where the parent waited during the sampled interval. The profile
does not sample solver children or identify their CPU hot spots. It is separate
from every timed sample.

The run makes no cold-cache, peak-memory, native execution, cross-language,
termination, or Rust-to-SMT correspondence claim. Verification remains
`smt-trusted`, and reported models remain unreplayed.

## Reproduce the corpus

The [configurable harness](../verification.py) was prepared after the measured
run. Its [manifest](../cases/verification/manifest.json) and nine source fixtures
match the recorded corpus; the wide unit-parameter fixture is generated
deterministically. A separate gate run validates the same 20 verification
outcomes and 64 evaluator outcomes. The harness also rejects deliberately wrong
outcomes, broken query hashes, incomplete query records and missing SAT models. Its later code is
not substituted for the original measured script in the snapshot.

Use Python 3, a POSIX host, the pinned Rust toolchain and the qualified Z3 5.3.3
release. Build the two exact revisions in separate checkouts, for example:

```sh
git worktree add --detach /tmp/apl-verify-before f8ffb5f128aab5eaed4db3770ae500cd923cc61c
git worktree add --detach /tmp/apl-verify-after 5e9dff071bf58a369af0386fb042c5948dcf8862
cargo build --release --locked --manifest-path /tmp/apl-verify-before/Cargo.toml
cargo build --release --locked --manifest-path /tmp/apl-verify-after/Cargo.toml
```

Run the harness from a checkout containing it. Select the actual solver path
through `APL_TEST_SOLVER` or replace that argument with a path. A rebuild on a
different host or at another build path may have a different binary hash. The
explicit hashes below pin those newly built binaries for the new run; they do
not make its timings interchangeable with this report.

```sh
python3 benchmarks/verification.py \
  --baseline /tmp/apl-verify-before/target/release/apl \
  --candidate /tmp/apl-verify-after/target/release/apl \
  --candidate-source /tmp/apl-verify-after \
  --solver "$APL_TEST_SOLVER" \
  --baseline-sha256 "$(shasum -a 256 /tmp/apl-verify-before/target/release/apl | cut -d ' ' -f 1)" \
  --candidate-sha256 "$(shasum -a 256 /tmp/apl-verify-after/target/release/apl | cut -d ' ' -f 1)" \
  --solver-sha256 "$(shasum -a 256 "$APL_TEST_SOLVER" | cut -d ' ' -f 1)" \
  --output target/verification-local.json.gz
```

Add `--gate-only` to check outcomes without timed sample rounds. The default
revision and executable hashes identify this report's original tools; explicit
hash options are needed for different builds. The harness verifies source
snapshots and tool identities before and after the run. These checks do not
independently attest that an arbitrary supplied binary was built from a claimed
revision, so retain the build commands and toolchain when publishing another run.
