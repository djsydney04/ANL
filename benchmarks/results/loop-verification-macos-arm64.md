# Invariant-loop verification coverage and latency

No demonstrated speedup or regression on four shared workloads; additional loop verification coverage is measured separately.

All rows use milliseconds as median [minimum, maximum] over five measured runs per side. One warmup round precedes the measurements. The 156 verification commands ran sequentially with alternating pair order; four shared workloads preserve complete normalized reports and exact SMT transcripts. Only compiler executable identity and the remaining-time SMT option are normalized. Proof-scope prose, models, status, metadata, and query contents remain compared.

## Shared supported routes

| Workload | Expected result | Queries | Baseline ms | Candidate ms |
| --- | --- | ---: | ---: | ---: |
| pure-affine | verified | 4 | 170.4 [165.7, 185.8] | 169.0 [166.9, 189.5] |
| pure-false-post | failed | 3 | 157.7 [155.8, 186.5] | 159.0 [157.7, 162.8] |
| state-scope | verified | 5 | 179.1 [176.5, 196.5] | 176.9 [176.0, 189.8] |
| state-intermediate-overflow | failed | 2 | 146.9 [145.5, 153.7] | 147.0 [145.5, 220.4] |

Median differences are smaller than the observed run-to-run ranges. Five samples on this loaded host do not establish a reliable speedup or regression. No component profile attributes costs to hashing, generation, solver work, or output.

## Added loop coverage

The baseline rejects every workload below before tool discovery, with zero solver queries. Its rejection latency is retained in the raw artifact for completeness and is not compared to proof latency. Candidate costs are:

| Workload | Candidate result | Completed queries | Expanded visits | Query bytes | Candidate ms |
| --- | --- | ---: | ---: | ---: | ---: |
| counter | verified | 15 | 81 | 57628 | 268.6 [265.7, 281.5] |
| final-false-write | verified | 7 | 35 | 23512 | 196.8 [193.4, 207.9] |
| safe-divergence | verified | 5 | 9 | 6584 | 172.2 [169.2, 173.2] |
| weak-invariant | failed | 5 | 20 | 10016 | 175.5 [174.3, 311.6] |
| trap-before-divergence | failed | 4 | 15 | 6143 | 165.6 [162.0, 220.3] |
| trap-after-divergence | verified | 4 | 10 | 5683 | 163.1 [161.4, 177.9] |
| missing-invariant | unsupported | 0 | 0 | 0 | 2.8 [2.6, 5.7] |
| nested-untouched | verified | 13 | 115 | 138305 | 255.3 [251.4, 297.4] |
| loop-work-cap | unknown | 35 | 318 | 3189025 | 707.6 [684.1, 756.4] |

The loop corpus includes finite calls, final false-guard mutation, safe divergence, a weak invariant, traps before and after divergence, a missing annotation, nested loops with an untouched mutable cell, and a unit-heavy work limit. The weak invariant fails despite a concrete result of 2. Safe divergence has no proved terminating execution. The resource case reaches `unknown` with exact message `symbolic work exceeds 1000000 units`, 35 completed verified leaf queries, 45 zero-symbol loop occurrences, and 318 expanded visits. It stops during leaf query processing and never begins the caller expansion.

## Correctness and reproducibility gates

Before timing, 26 verification invocations and 50 interpreter/check/native commands passed. Expected statuses, exits, query counts and order, source/tool identities, model shapes, abstract-head provenance, complete SMT transcripts, and failure causes are checked on every timed invocation. The independent oracle parses SMT definitions to reconstruct dependencies and exact guarded conjunctions. For the work limit it checks the exact submitted 35-query prefix; it does not claim the unsubmitted groups completed. Six deliberate in-memory corruptions of status, query hash, completion, SAT model, manifest, and guard metadata were rejected.

Finite outputs and traps were checked through real CLI execution. All 13 [fixtures](../cases/loop-verification/manifest.json) retain the bytes used for the measurements. The work fixture contains 2,000 unit parameters and 45 false loops. Its exact 35-query prefix was frozen before timing; the remaining pending leaf queries and the caller expansion are not represented as completed work. This is not a witness of a per-function budget reset.

The measured commands completed 696 solver queries and retained 21,082,236 query bytes in total. Every expected failure/unknown/unsupported outcome is counted as its own category. There were no unexpected errors or outer timeouts.

The production source, baseline/candidate/solver binaries, harness, oracle, and fixtures were hashed before and after. Source and tool hashes did not change. Raw command records contain argv, exact stdout/stderr, exit, wall time, child user/system CPU, query count/bytes, and expanded visits. The raw gzip retains every JSON report.

## Environment and limits

Host: hw.model: Mac16,10; hw.ncpu: 10; hw.physicalcpu: 10; hw.memsize: 34359738368. Platform: Darwin 25.4.0 arm64. Measurement started 2026-11-17T13:02:46.840340+00:00.
Load average changed from [4.77392578125, 5.98681640625, 7.6923828125] to [5.701171875, 6.08740234375, 7.677734375]. Other compiler builds were held during trials; an external VM used about 313% CPU at the start. Pair order and corpus order alternate to reduce drift, but this is not an idle-host or cross-platform experiment.
Both executables are frozen release copies. Baseline size is 1,119,968 bytes; candidate size is 1,255,440 bytes, a 135,472-byte increase. Z3 is the pinned 5.3.3 binary. Rust 1.99.1, Cargo 1.99.1, Apple clang 21.0.0 and Python 3.9.6 were present. Hardware, clock resolution/source, CPU process snapshots, and exact identities are retained in the [summary](loop-verification-macos-arm64-summary.json) and [raw artifact](loop-verification-macos-arm64.json.gz).

Each CLI verification uses a 30-second total verifier budget and a 45-second outer timeout. Time covers process start through complete JSON output. Validation, JSON parsing, oracle reconstruction, and artifact compression are outside the measured region. Child CPU is the operating system RUSAGE_CHILDREN delta, including waited-for descendants as reported by the OS; no per-component CPU claim is made.

No heap or component profile was collected. No Rust/source/SMT/solver correspondence theorem follows from these measurements. Existing large head-limit correctness cases were not repeated as timing workloads.

## Source and tool identities

The baseline compiler inputs match `0795dd689c40b88d0a0ae37e25bfdc3b06468f8e`.
The candidate inputs match `14bb053ca5e09f6036e1a61089452f8ccf90d375`.
The candidate executable was measured from the frozen source before that source
was committed; the published snapshot checks the file-by-file relationship to
the commit. Timing data was not rerun or relabeled during publication.

| Tool | Recorded bytes | Recorded SHA-256 |
| --- | ---: | --- |
| Baseline release CLI | 1119968 | `9a61fd95d4598082d60e914f1d3128e8b6d6a499a351cc2bc495587114b58a19` |
| Candidate release CLI | 1255440 | `7e6d0787aca17b770ad3043faf1ac3846adf39ee298b7c24e3a3b6a67fb4e013` |
| Z3 5.3.3, macOS arm64 | 32423904 | `9b3df8db3324ac2de9ebdd2841477366ecad0626656f806c2168ebf2732745a4` |

The [snapshot](loop-verification-macos-arm64-snapshot.json.gz) contains exact
compiler input hashes at both revisions, the original measured harness text and
hash, original gate freeze, and a mechanical mapping to the public harness.
The report oracle and all fixture bytes are identical. The public manifest drops
only unused original-location notes. Timing, report normalization, resource
prefix checks and deliberate report corruptions are unchanged; validation and
runtime helpers have only path substitutions. CLI configuration, source
identity checks and portable host metadata are outside the measured region.

The [raw gzip](loop-verification-macos-arm64.json.gz) is the original file,
SHA-256 `6eb053babac4af0fae69913d7e413f286ec9ee16b776e105ac6c389ccfc5a641`.
The [original gates gzip](loop-verification-macos-arm64-gates.json.gz) is also
unchanged, SHA-256 `4ad6b9da68a10c8158e261d8ccaafcbc0d4c222b029467dd3aa52bfb908395a7`.
Absolute paths inside those records identify historical commands. Public replay
does not open those original locations or import their scripts. The
[summary](loop-verification-macos-arm64-summary.json) retains all 26 wall and child
CPU median/range groups; the tables above display wall time only.

The relocated public harness was validated separately with the pinned binaries:
26 verification and 50 runtime checks passed, all six report corruptions were
rejected, and seven CLI identity/configuration failures were rejected before
execution. All 26 reports match the original gates after relocating source paths
and applying the original compiler-identity/timeout normalization. The
[public gate records](loop-verification-public-gates.json.gz) and
[publication validation](loop-verification-public-validation.json) preserve this
check. Those full gate records precede the stricter checkout-presence check.
A follow-up identity-only validation rejects 24 changed checkout configurations
across both source roles, including added build scripts, both Cargo config names,
legacy toolchain selection, missing pinned files and symlink/non-regular inputs.
Exact new-host and recorded-tool configurations pass. The semantic gates,
fixtures and measured command loop are unchanged; no timing trials were rerun.
These records are validation evidence, not replacement timing samples. The
[artifact manifest](loop-verification-artifacts.json) records the published
file hashes and excludes its own hash to avoid a circular reference.

## Replay with the recorded executable bytes

Use Python 3.9 or later on a POSIX host with Git, Rust/Cargo, clang and the
selected solver available. The recorded executable bytes require compatible
macOS arm64. The repository must contain both Git revisions; the candidate
source checkout must have the pinned compiler and test inputs. Additional
baseline checkout verification is available with `--baseline-source`.
The harness uses only the Python standard library and the adjacent
[report oracle](../loop_report_oracle.py).

From the repository root, replace these three executable paths:

```sh
python3 benchmarks/loop_verification.py gate \
  --baseline /absolute/path/to/baseline-apl \
  --candidate /absolute/path/to/candidate-apl \
  --solver /absolute/path/to/z3 \
  --output-dir target/loop-verification-recorded-tools

python3 benchmarks/loop_verification.py time \
  --baseline /absolute/path/to/baseline-apl \
  --candidate /absolute/path/to/candidate-apl \
  --solver /absolute/path/to/z3 \
  --output-dir target/loop-verification-recorded-tools
```

`gate` requires a fresh output directory. It runs 26 verification checks, 50
runtime/check/native checks, and six negative report gates, then records
`gates.json.gz` and `freeze.json`. `time` requires that accepted freeze and no
existing `raw.json.gz`. It records one warmup plus five alternating sequential
pairs for every case, repeats the semantic gates on every command, and writes
all samples and summaries to `raw.json.gz`. It hashes sources, tools and harness
inputs before and after the run. A changed identity, unexpected result, missing
model, wrong query, outer timeout or disabled Python assertion gate rejects the
run. Rejected command reports and partial run evidence remain in the new output
directory after verification begins. There is no machine-dependent pass/fail
latency threshold.

The four common workloads compare complete normalized reports between both
executables. Within each run, normalization changes only compiler executable
identity and the remaining-time SMT option; proof fields, source metadata,
models and all other query text remain compared. The independent oracle also
checks the loop report's exact guarded conjunctions and model dependencies.

## Build and record new executable identities

A new build path, toolchain, linker or host can produce different executable
bytes. The harness never accepts those bytes as the recorded binaries. Build
the same pinned source revisions separately, for example:

```sh
git worktree add --detach target/loop-baseline 0795dd689c40b88d0a0ae37e25bfdc3b06468f8e
git worktree add --detach target/loop-candidate 14bb053ca5e09f6036e1a61089452f8ccf90d375
cargo build --release --locked --manifest-path target/loop-baseline/Cargo.toml
cargo build --release --locked --manifest-path target/loop-candidate/Cargo.toml
```

Use the Rust 1.99.1 toolchain declared by both checkouts. Cargo dependencies must
be available; building them is outside the measured interval. Compute and
inspect the SHA-256 of each resulting executable and the selected solver, then
supply all three hashes explicitly. `--new-host` identifies a new experiment
with the same source/corpus and strict semantic gates; it does not reproduce or
replace the historical timing values. It requires both source checkouts and
rejects changed checkout-local compiler inputs even when custom executable
hashes are supplied. It compares the full file set under `src/` and `.cargo/`,
plus root `Cargo.toml`, `Cargo.lock`, `build.rs`, `rust-toolchain` and
`rust-toolchain.toml`, with the pinned snapshot. Added, missing, changed,
symlinked or non-regular inputs are rejected, including the legacy
`.cargo/config` filename. The two additional pinned candidate test files remain
hashed as well.

```sh
python3 benchmarks/loop_verification.py gate --new-host \
  --baseline target/loop-baseline/target/release/apl \
  --candidate target/loop-candidate/target/release/apl \
  --solver /absolute/path/to/z3 \
  --baseline-source target/loop-baseline \
  --candidate-source target/loop-candidate \
  --baseline-sha256 BASELINE_SHA256 \
  --candidate-sha256 CANDIDATE_SHA256 \
  --solver-sha256 SOLVER_SHA256 \
  --output-dir target/loop-verification-new-host
```

Replace the three uppercase placeholders with lowercase 64-digit hashes.
After gates pass, repeat the same command with `time` in place of `gate` and the
same flags. The new artifacts retain supplied hashes, source paths, host
metadata and their own timings. Binary hashes and matching source bytes identify
the inputs; they are not a formal proof that a binary was built from that source.
The checkout checks do not establish a hermetic build: environment variables,
installed compiler/linker/SDK and dependency-cache contents, rustup overrides,
and Cargo configuration outside the selected checkout are not attested.
[Cargo configuration](https://doc.rust-lang.org/cargo/reference/config.html)
depends on the build invocation directory and its ancestors/global configuration;
[rustup overrides](https://rust-lang.github.io/rustup/overrides.html) can also
select a toolchain independently. Record these conditions for a new experiment;
`--new-host` records supplied executable identities rather than attesting how the
executables were built.
