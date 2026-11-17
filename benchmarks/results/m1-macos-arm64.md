# M1 local baseline

This is an initial end-to-end CLI baseline, not evidence of a speedup. Optimization
comparisons are inconclusive because there is no earlier comparable compiler
measurement or isolated compiler-internal profile.

The release binary was built from commit
`14f2defa5e01870865364934193851ccbe6a9fe9` using
`cargo +1.99.1 build --release --locked` and measured at
`2026-11-17T07:25:14.542284+00:00`. The host ran macOS
(Darwin 25.4.0), arm64, with 10 logical CPUs and Rust 1.99.1.
The one-, five-, and fifteen-minute load averages were 5.73, 7.42, and 7.74
at both the start and end of the run. A virtual machine and Python process were
active before measurement. This was a shared host, not an idle benchmark machine.

Every compiler source file, Cargo manifest and lockfile, benchmark script,
manifest, and case fixture matched the recorded Git revision before and after
the run. The report marks the worktree dirty because documentation edits and
untracked benchmark result and ignore files were present. Those changes did not
alter the compiler or benchmark inputs. The exact hashes are:

| Artifact | SHA-256 |
| --- | --- |
| Compiler source digest | `c76a47157dff7a7a9396f600f2d110f4fbffa48c8fb3a9e760bdda8e1aa117a1` |
| Release binary | `ba7f7d2f066bf67cf6c67cd5b6de9dfddb2101820a28589564ed235e132594e9` |

The [full report](m1-macos-arm64.json) retains the two warmup rounds, seven measured
samples per command, outputs, exit statuses, CPU times, fixture hashes, and host
metadata. All 20 case/operation combinations passed a separate semantic preflight.
Every subsequent timed invocation matched its explicit expectation, including
four jobs whose expected behavior is a source rejection or named trap. There were
no unexpected failures or timeouts across all 207 timed and validated invocations,
including the startup control.

| Representative command | Median | Range, 7 samples |
| --- | ---: | ---: |
| Evaluate Fibonacci(18), result 2584 | 2.453 ms | 2.330–2.483 ms |
| Check a 200-function module | 2.192 ms | 2.160–2.468 ms |
| Evaluate factorial(10), result 3628800 | 2.075 ms | 1.896–2.246 ms |
| Print compiler version, startup control | 1.913 ms | 1.865–1.998 ms |

Most small-case timings are close to the process-startup control. The data do not
isolate interpreter or parser cost, and subtracting the control would amplify
scheduling noise. No internal bottleneck was established by profiling. The
measured region includes process launch, source reading, parsing, checking,
optional evaluation, and complete output capture. Each result is checked before
its sample is accepted. OS caches are warm after preflight and warmups.

This records one release binary on one macOS host. These measurements do not
establish Linux latency, cold-cache behavior, peak memory, larger-workload
performance, native execution performance, external compiler comparisons, or
compiler correctness beyond the checked fixtures.
