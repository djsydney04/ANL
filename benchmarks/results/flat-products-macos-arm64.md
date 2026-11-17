# ANL flat-product measurements — macOS arm64

The fixed-payload representation reduced tuple-loop median times in these runs, while retaining many distinct singletons increased interpreter peak RSS by **42.1%**. Scalar arithmetic evaluation remained **6.3–9.4% slower in median** than the pre-tuple compiler. Fresh-process export review flags remain recorded; a separate warm in-process probe does not erase them. These are workload-specific observations on one shared host, not a general performance or memory-efficiency claim. The fixed-payload implementation was retained with these measured costs as an explicit tradeoff. That decision does not clear the raw `review_required` flags or establish the cause of the recurring export cost.

The fixed-payload subject is bound to semantic checkpoint `45790f05f769af8bc3e31c82bcca0e98f1e2eb21`, before the CLI/crate naming migration. The pre-tuple and initial Arc-slice subjects have separate identities below. That checkpoint builds the historical `apl` executable. ANL is the current language name; these results do not identify the later renamed `anl` binary. Historical `.apl` inputs and `apl-*` wire identifiers remain exact evidence.

## Comparisons and every official run

The scalar comparison uses pre-tuple commit `14bb053ca5e09f6036e1a61089452f8ccf90d375`. The initial Arc-slice feature implementation is an unpublished source variant, identified by source digest `e0bbf593…` and binary SHA-256 `960c6732…`, not a Git commit. It is reproduced by applying the checked-in [evaluator patch](../cases/flat-products/arc-slice-variant.patch) to checkpoint `45790f05`. The fixed-payload implementation has source digest `6c35db93…` and binary SHA-256 `db18624e…`. Complete identities are in [source bindings](flat-products-sources.json).

The first two scalar runs identified costs that led to rejection of the initial Arc-slice implementation. Those measurements remain valid and are retained in full. Four subsequent scalar runs use the fixed-payload implementation. The tuple and retained-allocation comparisons use the two feature-capable implementations; pre-tuple rejection time is never a tuple-throughput baseline. No official run or flagged observation has been discarded.

| Official run | Semantic invocations | Measured child invocations | Recorded review flags |
| --- | ---: | ---: | --- |
| `scalar-paired-e0bbf593-01` | 144 | 336 | `arithmetic-loop/emit-c/wall_ns`; `arithmetic-loop/eval/wall_ns`; `calls-locals-branches/eval/wall_ns` |
| `scalar-paired-e0bbf593-02` | 144 | 336 | `arithmetic-loop/eval/wall_ns`; `calls-locals-branches/eval/wall_ns` |
| `scalar-optimized-db18624e-01` | 144 | 336 | None above the investigation thresholds |
| `scalar-optimized-db18624e-02` | 144 | 336 | `branching-recursion/dump-core/wall_ns`; `arithmetic-loop/emit-c/wall_ns`; `calls-locals-branches/emit-c/wall_ns` |
| `scalar-optimized-db18624e-03` | 144 | 336 | None above the investigation thresholds |
| `scalar-optimized-db18624e-04` | 144 | 336 | `arithmetic-loop/emit-c/wall_ns` |
| `tuples-optimized-db18624e-01` | 108 | 168 | None; observation-only tuple policy |
| `tuples-optimized-db18624e-02` | 108 | 168 | None; observation-only tuple policy |
| `retained-optimized-db18624e-01` | 52 | 112 | None; observation-only tuple policy |
| `retained-optimized-db18624e-02` | 52 | 112 | None; observation-only tuple policy |

Each run uses two warmup rounds and seven measured pairs per case/operation. Scalar ratios above 1.10 for median wall time or 1.15 for median RSS trigger investigation; these thresholds are not statistical acceptance tests or proof of no regression. Tuple measurements have no invented pass/fail threshold. All flags stay in the [run index](flat-products-run-index.json) and [complete summaries](flat-products-macos-arm64-summary.json).

## Scalar evaluation and export costs

The six scalar cases cover a constant, branching recursion, a million-step arithmetic loop, 200 functions, calls/locals/branches, and a 33-file graph containing 1,025 functions. Candidate/baseline median wall ratios for `eval` are:

| Workload | Initial 01 | Initial 02 | Optimized 01 | Optimized 02 | Optimized 03 | Optimized 04 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| constant-control | 1.0157 | 1.0103 | 1.0436 | 1.0146 | 0.9901 | 0.9713 |
| branching-recursion | 1.0371 | 0.9943 | 1.0398 | 0.9757 | 1.0055 | 0.9854 |
| arithmetic-loop | 1.3025 | 1.3063 | 1.0839 | 1.0939 | 1.0633 | 1.0769 |
| many-functions | 1.0128 | 1.0076 | 1.0133 | 1.0150 | 0.9326 | 0.9720 |
| calls-locals-branches | 1.1411 | 1.1260 | 1.0119 | 1.0114 | 1.0088 | 1.0510 |
| module-graph-32x32 | 1.0263 | 1.0344 | 1.0646 | 1.0575 | 1.0374 | 0.9973 |

The table above shows evaluation only; all four operations (`check`, `dump-core`, `emit-c`, `eval`), their ranges, CPU times and RSS remain in the complete summary and raw records. The recurring arithmetic-loop observations are shown below in milliseconds, median [minimum, maximum]:

| Fixed-payload run / operation | Pre-tuple baseline | Fixed payload | Ratio |
| --- | ---: | ---: | ---: |
| 01 / eval | 54.720 [54.507, 56.535] | 59.310 [58.152, 60.506] | 1.0839 |
| 01 / emit-c | 2.678 [2.419, 3.322] | 2.865 [2.544, 4.044] | 1.0698 |
| 02 / eval | 55.791 [55.582, 76.318] | 61.029 [58.753, 85.600] | 1.0939 |
| 02 / emit-c | 2.849 [2.397, 3.503] | 3.288 [2.472, 6.895] | 1.1542 |
| 03 / eval | 56.221 [53.736, 63.127] | 59.778 [58.141, 62.064] | 1.0633 |
| 03 / emit-c | 2.820 [2.563, 3.388] | 3.035 [2.571, 4.957] | 1.0762 |
| 04 / eval | 54.812 [53.835, 58.574] | 59.026 [58.249, 78.808] | 1.0769 |
| 04 / emit-c | 2.825 [2.445, 4.780] | 3.197 [2.485, 3.503] | 1.1319 |

The export wall medians increased by 187–439 µs (0.187–0.439 ms), with overlapping ranges in every run; two exceed the frozen 10% investigation trigger. Their recurring direction is not dismissed as noise. Fresh-process startup, cold execution, filesystem and scheduling effects were not separately measured. Smaller per-helper costs do not prove that the CLI cost has disappeared.

A separate [warm export probe](flat-products-export-probe.json.gz) contains one fixed seven-round run with 500 warmup iterations and 20,000 operations per phase. It links the exact-source release libraries and checks complete expected C output before timing, then consumes each result and checks length/checksum. Arithmetic compilation medians were 4.179→4.464 µs; lowering/validation plus emission were 6.466→2.887 µs; combined work was 10.796→7.432 µs (ranges 10.653–11.706 and 7.316–7.529 µs). Product detection was about 45 ns in that warm fixture. Direct formatting into the output buffer avoids old temporary formatting strings, consistent with improved warm emission. The probe excludes CLI launch, source-file loading and output publication; it neither explains the whole process delta nor replaces any official flag. Its source, exact input/library identities, raw observations and protocol are included.

## Tuple workloads and retained memory

The pair loop performs 200,000 replacements/calls and checks prior snapshots, returning 20,000,500,001 after 400,002 constructed fields. The mixed eight-field loop performs 100,000 replacements with integer, bool and unit checks, returning 1,100,006 after 800,008 fields. Both stay below the 1,048,576 field budget, with peak logical slot bounds of eight and seven. A small tuple-returning API and an effectful argument-capture fixture provide control/correctness cases.

Wall milliseconds for the substantive tuple evaluation workloads:

| Run / case | Arc slice | Fixed payload | Ratio |
| --- | ---: | ---: | ---: |
| 01 / pair-calls-state-200k | 74.830 [73.778, 76.681] | 66.554 [63.253, 70.171] | 0.8894 |
| 01 / mixed-eight-state-100k | 46.511 [46.051, 47.273] | 41.692 [40.374, 42.489] | 0.8964 |
| 01 / retained-singletons | 5.804 [4.451, 12.784] | 6.541 [4.872, 14.685] | 1.1269 |
| 01 / scalar-control | 4.650 [3.335, 5.196] | 3.805 [3.207, 4.651] | 0.8182 |
| 02 / pair-calls-state-200k | 81.903 [74.671, 112.068] | 67.384 [65.625, 188.617] | 0.8227 |
| 02 / mixed-eight-state-100k | 52.135 [45.614, 92.108] | 47.598 [40.135, 74.160] | 0.9130 |
| 02 / retained-singletons | 4.558 [3.814, 5.147] | 4.392 [4.072, 4.978] | 0.9636 |
| 02 / scalar-control | 3.727 [3.295, 4.332] | 3.628 [3.232, 5.279] | 0.9733 |

Tuple-loop medians are lower in both runs, but the second run has wider variation. Retained-singleton timing changes direction between repetitions. No broad speedup claim follows.

The retained fixture deliberately holds 64 frames × 256 separately constructed singleton payloads: **16,384 payloads** and **16,448 argument cells** at the deepest call. It returns 257. The matching scalar control has the same call/argument topology. Exact interpreter fuel is independently derived and checked: 65,539 entries for tuples and 49,153 for scalars; one less fails on both binaries. Maximum evaluator depth indices are 130/129, below 256, and the tuple case stays below both logical resource limits.

Both retained runs report the same median tuple-process RSS: **4,472,832→6,356,992 bytes**, an increase of 1,884,160 bytes (42.1%). This is whole-child peak RSS, not an isolated heap measurement. The scalar control is reported alongside it; different source/core shapes mean subtracting the two RSS values would not isolate payload memory.

Independent [host allocation probes](flat-products-allocation-probe.json.gz), linked to debug libraries from the exact sources on Rust 1.99.1/aarch64 macOS, observed singleton requests of **32→152 bytes**, aligned to eight. The fixed representation requests 152 bytes at every arity, whereas the Arc-slice request is 16+16×arity. Host `Value` size changes **24→16 bytes**. Cloning requests no new allocation and the final owner frees once. These observations concern those external probes, not instrumentation of the measured release executables.

Applying per-constructor sizes to this fixture gives **derived** tuple-request totals of 524,288→2,490,368 bytes. Retained cell storage is 394,752→263,168 bytes using the measured host layouts. These calculations omit allocator rounding/metadata, stacks, parser/core storage and other allocations. They are not observed allocation totals, total live heap measurements, RSS proofs, portable ABI guarantees, or hard memory bounds. The smaller handle trades increased narrow-tuple payload cost for reduced value-cell size.

## Correctness, native code and measurement boundary

Across the ten official runs, 1,184 semantic invocations and 736 warmup invocations precede or accompany 2,576 measured child invocations. There were zero unexpected failures. Independent expected results, expected source rejections and traps are checked; each measured command must reproduce its preflight output. Source checks/evaluation, typed core evaluation, exact core/C export identity, and native C11 compilation/link/execution at O0 and O2 protect the comparison. Snapshot order, typed tuple JSON results and exact-fuel witnesses are semantic checks, not timed rejection workloads.

Every baseline/candidate pair emits byte-identical core and C for its supported frozen workloads. Native object/executable sizes are retained and checked for growth; the comparisons did not grow them. No native throughput trials are included. The host-interpreter Arc representation is absent from the generated by-value C tuples, so the retained-RSS result is not a native C heap measurement or a reason to infer a native slowdown.

The standard-library Python controller measures process launch through completion with `perf_counter_ns`, per-child CPU and peak RSS from `os.wait4`. Darwin RSS is bytes; Linux conversion is explicit. Source `eval` includes parsing, checking and lowering. Check/export controls are often startup dominated. Output validation, hashing and compression occur outside the measured interval. Each child has a 120-second timeout and a 64 MiB per-output-file limit. Warmups and samples alternate baseline/candidate order; job traversal reverses each round. No cold-cache, concurrency, native-throughput, cross-platform, full-language or formal-correctness result is claimed.

## Host and reproducible evidence

Recorded host: Darwin 25.4.0, arm64, ten logical CPUs; Python 3.9.6, Rust 1.99.1, Apple clang 21.0.0 and SDK 26.5. Trials used frozen release binaries and a coordinated pause in local builds, but the machine remained shared. The first initial-variant run began at load [4.792, 4.959, 5.579]; optimized run 01 began at [7.946, 11.262, 9.156], and optimized run 04 ended at [6.752, 9.030, 8.625]. Every run and round retains its load samples. These are not idle-host observations.

The [compressed raw archive](flat-products-macos-arm64.json.gz) contains all ten full reports, all 57 distinct stdout/stderr blobs, original and published hashes, and a field-level record of path normalization. Only location strings change to logical aliases. Numerical observations, outcomes, original hashes, source identities and review flags are retained. Original report hashes identify the pre-normalization files; redacted locations prevent reconstructing their original bytes from this archive alone. The published archive has its own integrity hash. No historical private path or copied compiler binary is required for replay.

The [measurement snapshot](flat-products-measurement-snapshot.json.gz) preserves the three original controller texts/hashes and exact evaluator texts needed to verify the variant patch. The public controller reuses the same wait4 executor and measured-round loop; configuration, source inventory checks, suite selection and output paths are adapted outside timing. Its focused integrity checks reject missing/extra build/config/source inputs, symlinks, changed output, altered retained-work recipes, omitted runs and corrupted observations. Typed JSON gates additionally reject duplicate keys and distinguish booleans from integer values; the archived typed outcomes and core exports were rechecked under these stricter publication gates. These checks validate packaging and measurement boundaries; they add no language proof claim.

[Source identities](flat-products-sources.json) cover complete checkout-local `src`, `.cargo`, Cargo manifests/lock, build scripts and both toolchain-selector names, rejecting added or missing selected inputs. Frozen test files are checked where captured. Ancestor/global Cargo configuration, environment-derived build flags, all SDK contents, and ambient toolchain state are not attested. Checked binary hashes plus matching source bytes do not themselves prove a build relationship; the recorded source/build binding was reviewed separately. A new build is explicitly a new experiment with its own binary/tool identities.

## Reproduce the historical comparison

Use Python 3.9+ and a POSIX host supporting `wait4`. Build the historical checkpoints separately using their pinned Rust 1.99.1 toolchain and locked dependencies. The current renamed checkout intentionally fails the historical source-identity gate. From a checkout containing both commits:

```sh
git worktree add --detach target/flat-pretuple 14bb053ca5e09f6036e1a61089452f8ccf90d375
git worktree add --detach target/flat-fixed 45790f05f769af8bc3e31c82bcca0e98f1e2eb21
git worktree add --detach target/flat-arc 45790f05f769af8bc3e31c82bcca0e98f1e2eb21
git -C target/flat-arc apply "$PWD/benchmarks/cases/flat-products/arc-slice-variant.patch"
CARGO_TARGET_DIR="$PWD/target/flat-pretuple-build" cargo +1.99.1 build --release --locked --manifest-path target/flat-pretuple/Cargo.toml
CARGO_TARGET_DIR="$PWD/target/flat-fixed-build" cargo +1.99.1 build --release --locked --manifest-path target/flat-fixed/Cargo.toml
CARGO_TARGET_DIR="$PWD/target/flat-arc-build" cargo +1.99.1 build --release --locked --manifest-path target/flat-arc/Cargo.toml
```

Those checkpoints produce `release/apl`, despite the current ANL name. Building is outside measured time. The Arc-slice patch changes only `src/eval.rs`; it is an exact source variant, not a fictitious revision. Compute and inspect the executable, C compiler and linker SHA-256 values before supplying the placeholders below. For example, use `shasum -a 256` on macOS or `sha256sum` on Linux.

First validate the published artifact and existing controller gates without invoking a compiler:

```sh
python3 benchmarks/flat_products.py audit
python3 benchmarks/flat_products.py self-test
python3 -m unittest discover -s benchmarks -p test_flat_products.py
```

For a new local experiment, substitute four inspected hashes and choose the actual C compiler/linker paths. This macOS example selects the SDK with `xcrun`:

```sh
python3 benchmarks/flat_products.py gate --suite scalar-optimized \
  --baseline target/flat-pretuple-build/release/apl --baseline-source target/flat-pretuple \
  --candidate target/flat-fixed-build/release/apl --candidate-source target/flat-fixed \
  --new-host --baseline-sha256 BASELINE_SHA256 --candidate-sha256 CANDIDATE_SHA256 \
  --cc "$(xcrun --find clang)" --cc-sha256 CLANG_SHA256 \
  --linker "$(xcrun --find ld)" --linker-sha256 LINKER_SHA256 \
  --sdk "$(xcrun --show-sdk-path)" --output-dir target/flat-public-gates
```

Use `validate` instead of `gate` to check identities without executing workloads. Once gates pass and the host is quiet, replace `gate` with `measure` and use a fresh output directory, for example `target/flat-public-run-01`. The runner repeats correctness preflight before timing. `--new-host` never redefines the historical identities; it records a separate experiment on the same exact source/corpus. The manifest fixes two warmups and seven pairs. Changed inputs, tool hashes, timeouts, wrong outputs or reused output directories reject a run; partial rejected evidence is retained after execution starts.

Suite selection preserves each comparison:

| Suite | Baseline checkout/binary | Candidate checkout/binary |
| --- | --- | --- |
| `scalar-initial` | `flat-pretuple` / `flat-pretuple-build` | `flat-arc` / `flat-arc-build` |
| `scalar-optimized` | `flat-pretuple` / `flat-pretuple-build` | `flat-fixed` / `flat-fixed-build` |
| `tuples` | `flat-arc` / `flat-arc-build` | `flat-fixed` / `flat-fixed-build` |
| `retained` | `flat-arc` / `flat-arc-build` | `flat-fixed` / `flat-fixed-build` |

To replay with byte-identical recorded tools, omit `--new-host` and supplied replacement hashes. The controller then requires the recorded binary/Python/C-compiler/linker identities, host family and selected SDK headers. Set `SDKROOT` to the selected SDK and restore the recorded environment values shown in [tool provenance](flat-products-recorded-tools.json). No absolute historical tool path is assumed. New source builds can differ in executable bytes because of paths, linking or configuration; use new-host mode rather than relabeling those binaries as historical ones.

The [publication validation record](flat-products-public-validation.json) records artifact, corruption, source-inventory and controller-preservation checks. An independent review copied the public package outside the checkout and replayed its frozen tools/sources: 144 scalar, 108 tuple and 52 retained semantic invocations passed, including native O0/O2 checks. All native-size comparisons were unchanged or smaller. The [normalized replay records](flat-products-public-gates.json.gz) bind the reviewed manifest and retain command/outcome evidence. These 304 untimed invocations add no performance samples, and no Cargo build was performed. The [artifact manifest](flat-products-artifacts.json) freezes the package and excludes its own hash to avoid circularity.
