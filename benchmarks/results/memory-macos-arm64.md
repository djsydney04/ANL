# Owned-buffer performance observations

The fixed run completed all 336 planned jobs on one shared macOS arm64 host. Its results are inconclusive about a general speedup or absence of regression. The unchanged recurrence evaluator had a **4.9% higher wall median** and tuple checking had a **17.1% higher wall median**. These costs remain in the report.

The [complete tables](memory-macos-arm64-tables.md) contain all 42 series with six-sample medians and min/max ranges for wall time, user CPU, system CPU, immediate-child peak RSS, full native file sizes, and comparison ratios. The [machine-readable summary](memory-macos-arm64-summary.json) retains exact values. The [compressed evidence](memory-macos-arm64-evidence.json.gz) retains commands, raw outputs, original file identities, all 84 warmups and 252 samples, native bindings, the historical failed attempt, and controller/source snapshots.

| Workload | Fixed completed work | Independent output |
| --- | --- | ---: |
| constant | Scalar startup/control program; may fold | 42 |
| recurrence | 1,000,000 Park–Miller updates | 1263606197 |
| tuple-calls | 200,000 pair snapshot/call/comparison/checksum iterations | 20000500001 |
| buffer-read | Fill 16,384 cells with 7; scan 64 times through a read view | 7340032 |
| buffer-edit | Fill 4,096 cells with 3; add index + 1 for 64 rounds; scan | 537014272 |
| buffer-owners | 16,384 calls that fill, read and release a 16-cell owner | 1834216 |

Every applicable eval/native result must be the decimal plus one LF, with exit 0 and empty stderr. Arithmetic expectations were sealed before execution. Allocation refusals, wrong values, traps, resource cutoffs, timeouts, or output errors invalidate the experiment. C is a comparison implementation, not OS code. The complete authored OS remains required to be ANL.

## Observed costs and limits

Recurrence `eval` wall medians were **61.630 → 64.628 ms** (ranges 59.527–66.824 and 62.757–69.667 ms). Its user CPU median increased from 57.016 to 61.260 ms, about 7.4%. Tuple `check` wall medians were **3.605 → 4.222 ms**, with wide, overlapping ranges of 3.313–17.136 and 3.533–21.959 ms. Its user CPU median changed by about 0.8%. These are retained observations; the experiment does not identify their causes.

Candidate buffer native medians were **3.584, 3.241, and 3.389 ms** for read, edit, and owners. Authored-C medians were 3.977, 3.349, and 3.362 ms. Candidate/C median ratios were 0.9012, 0.9678, and 1.0080. Read ranges narrowly do not overlap: candidate maximum 3.853417 ms versus C minimum 3.858750 ms. Edit and owner ranges overlap. The constant native control was about 3.1 ms, so process startup, output and exit are a large part of these short measurements. No startup cost was subtracted and no isolated per-read, per-write, or per-allocation speedup is claimed.

Full CLI buffer check medians were 3.37–3.54 ms. Eval medians were 62.20 ms read, 24.86 ms edit, and 6.43 ms owners. Build medians were 74.28–76.98 ms. C appears only in native comparisons; there is no comparison between the complete ANL build pipeline and a single C frontend stage. The C fixtures check signed arithmetic, allocation, index bounds and output, but do not implement ANL owner/loan validation, typed IR, interpreter metering or opaque runtime representation. The comparison covers the fixed successful inputs, not all failure paths or arbitrary programs.

The host was macOS 26.4.1 arm64 with 10 logical CPUs. One-minute load averages were 5.23 before gates, 5.35 before samples, and 5.82 afterward. Thermal queries exited 0 and reported no recorded warning level; this does not prove absence of throttling. The host was shared. There was no cache flush, retry, sample exclusion, adaptive input resizing or profiling. These micro workloads are not OS/application end-to-end measurements, and no bottleneck or universal performance conclusion follows.

## Correctness and measurement boundary

The original controller checked source/eval outcomes, exact control Core/C equality, actual buffer Core/MIR pairs, and small formal reference companions before timing. Six pair reports accepted the three measured buffers and three companions. The companions have exact results 224/168/76, full allocation request/release traces, and zero live cells and active slots at completion. Large measured workloads were not reference-evaluated; they retain their actual pair gates and independent completed outcomes.

All three unchanged controls emit identical Core/C and native binary bytes across baseline and candidate. Fifteen native binaries and 15 actual C-compiler calls bind the compiled inputs. All 72 timed build artifacts match the associated captured default native binary hash and size; their native outcomes were checked outside the timed build interval. Buffer builds use separate production C11 `-O2 -fno-lto` program/runtime compilation and a separate link. There is no memory-evidence native compilation flag or trace/replay environment in the measurements.

The standard-library controller measures process launch through exit with `perf_counter_ns`, CPU and peak RSS from `wait4`. Darwin RSS is bytes for the reaped immediate child, not summed simultaneous process-tree memory. Build CPU accounting can include reaped compiler children. Native sizes are full executable bytes. First launches and gates are untimed. Every series has two warmups and six samples; pairs alternate order and three-side native controls exhaust all six permutations. Case traversal reverses each round.

The [public controller](../memory.py) preserves the original `execute` and `Experiment.measure` text, and the remaining semantic/capture boundaries are checked by the [preservation record](memory-controller-preservation.json). Configuration changes supply explicit tool/source paths, public protocol helpers, a Python-bound CC adapter launcher, package auditing, and fresh gate/experiment output directories. Those changes occur outside timed intervals. The [offline validation record](memory-public-validation.json) records archive, normalization, fault-rejection and synthetic entrypoint checks. No public gate or fresh measurement is claimed here.

## Failed preparation retained

V1 had a host-context exit handling defect. V2 added the missing exit check; ten offline synthetic cases cover failures at all nine context positions and a successful query with a notice. The initial discriminator attempt and correction are retained in historical preparation evidence; it was not a timing run.

The actual V2 experiment executed **49 untimed commands**, with 48 successes, then failed checking the first buffer source. Six authored fixtures used unparenthesized `while` conditions and trailing while-block semicolons rejected by the existing parser. It collected **zero warmups and zero samples**. V3 repaired only those six fixture syntax forms. Numeric inputs, C, oracles, and schedule stayed fixed. Exactly **nine presealed check-only qualifications** passed before the separately authorized completed V3 experiment. The failed attempt has not been erased or treated as measurement data.

## Audit and a new experiment

From the repository root, Python 3 can inspect the published evidence without launching project tools:

```sh
python3 benchmarks/memory.py audit
```

A successful audit reports 568 historical experiment commands (519 completed V3 and 49 failed-attempt V2), 336 measurement records, 252 samples, 42 summaries, and the offline rejection checks. The nine check-only syntax qualifications are separately retained.

For a new run, prepare a baseline checkout at `f63a0526d4978712a6ae7d05b9c18a83bcbf78e0` and a candidate tree matching the exact 52-file [source inventory](memory-sources.json). Build the baseline release `anl`, the candidate default release `anl`, and the candidate `memory_evidence` example with its feature enabled. Build the pair/reference tools using the [formal setup](../../formal/README.md#owned-buffers-and-memory-artifacts). Supply each actual executable SHA-256 explicitly; a different build path, binary, source, or host does not inherit the historical timings. The runner requires the recorded source files and records a new experiment with the selected tool bytes. It does not build the tools or certify that an arbitrary binary was compiled from the supplied source.

With the matching baseline checkout already prepared, these commands build separate tool outputs; they are reproduction instructions, not commands executed for this publication:

```sh
cargo build --release --locked --manifest-path /path/to/baseline/source/Cargo.toml --target-dir target/memory-baseline
cargo build --release --locked --target-dir target/memory-default
cargo build --release --locked --features memory-evidence --example memory_evidence --target-dir target/memory-exporter
(cd formal && lake build anl_memory_pair_checker anl_memory_reference_runner)
```

The resulting paths are `target/memory-baseline/release/anl`, `target/memory-default/release/anl`, `target/memory-exporter/release/examples/memory_evidence`, `formal/.lake/build/bin/anl_memory_pair_checker`, and `formal/.lake/build/bin/anl_memory_reference_runner`. The baseline target directory is interpreted by Cargo relative to the calling directory; use an absolute target directory when preparing it elsewhere.

A macOS gate invocation has this shape; substitute inspected paths and hashes:

```sh
python3 benchmarks/memory.py gate \
  --baseline /path/to/baseline/anl --baseline-sha256 BASELINE_SHA256 \
  --baseline-source /path/to/baseline/source \
  --candidate /path/to/candidate/anl --candidate-sha256 CANDIDATE_SHA256 \
  --candidate-source /path/to/candidate/source \
  --exporter /path/to/memory_evidence --exporter-sha256 EXPORTER_SHA256 \
  --pair /path/to/anl_memory_pair_checker --pair-sha256 PAIR_SHA256 \
  --reference /path/to/anl_memory_reference_runner --reference-sha256 REFERENCE_SHA256 \
  --cc /path/to/clang --cc-sha256 CLANG_SHA256 \
  --linker /path/to/ld --linker-sha256 LINKER_SHA256 \
  --sdk /path/to/MacOSX.sdk --output-dir target/memory-gates-01
```

The linker must be the `ld` in the selected compiler directory. `gate` runs untimed semantic/native preflight and host context only. `experiment` uses the same arguments with a fresh output directory and repeats all gates before the fixed 336-job measurement schedule. Failed or interrupted runs preserve partial records and cannot restart in the same directory. Both commands execute project/native tools; neither is part of the read-only audit. Other operating systems require a reviewed context-command adaptation. No machine-dependent latency threshold or automatic speedup verdict is built in.

## Archive identities

The gzip JSON uses deterministic compression with mtime 0. Each entry records the original size/hash and either normalized UTF-8 content with its own size/hash or an explicit identity-only binary/object omission. Generated C and runtime headers remain present. A field-level ledger records each JSON path, text-line or UTF-8 hex source-path normalization. Original hashes identify original captures; normalized bytes have their own identities and cannot reconstruct the original private paths byte for byte. The [artifact manifest](memory-artifacts.json) binds the public package and its shared protocol helpers and excludes its own hash. Host kernel, libraries, Python standard library and the transitive SDK remain trusted host inputs.
