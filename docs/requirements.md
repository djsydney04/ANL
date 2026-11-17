# Language requirements

ANL targets a complete systems language and development environment. The
[language charter](charter.md) defines its purpose and the [roadmap](roadmap.md)
orders delivery. This specification lists the capabilities and evidence needed
for a release. The current implementation covers parts of these requirements; the
coverage record below does not close any complete-language release requirement.

Evidence categories are distinct. **Designed** means a specification exists.
**Implemented** means executable code exists. **Tested** identifies passing checks.
**Machine-checked** names the theorem, formal model, tool version and assumptions.
**Released** requires qualified installation artifacts. None implies another.

## OS authorship and expressibility gate

**Open; mandatory for project completion and final release.** In addition to the
52 technical requirement IDs below, the complete operating system must be
authored in ANL: boot code, hardware initialization, interrupt handlers, memory
management, scheduler, drivers, filesystems, networking, system services, agent
infrastructure and GUI. This gate spans language, compiler, runtime and product
requirements; hosted OS access under L14 or S02 does not satisfy it.

Missing expressibility is a language/compiler gap to close. ANL must provide
features or intrinsics for register access, interrupt entry/return, atomics,
barriers, port I/O and page-table manipulation, with explicit semantics and
documented safety boundaries. The compiler may initially be implemented in Rust
and may emit C. Generated output must not conceal handwritten C/Rust OS
functionality. Foreign interoperability is not an exception to OS authorship.

Firmware and an external bootloader may support initial bring-up through explicit
boundaries. Boot responsibilities within the intended OS scope must be developed
in ANL. Any temporary handwritten assembly or other non-ANL OS code must be
minimal, identify a concrete missing language/compiler capability, and carry an
ANL replacement plan. Each milestone must report every remaining instance until
eliminated. Convenience is not a reason to retain non-ANL OS implementation.

Acceptance requires:

- An integrated bootable OS exercising every listed subsystem from ANL source,
  with target-specific conformance, failure, isolation and security evidence.
- A source-to-artifact inventory of OS code, generated code, linked dependencies,
  firmware and bootloader boundaries, and the trust assumptions for each.
- Specified hardware operations and checked compiler lowering, supported by
  executable target evidence; formal claims remain limited to named models.
- Elimination of temporary non-ANL OS implementation before completion or final
  release, with the final audit recording how each missing capability was closed.

The [OS architecture](architecture/operating-system.md) defines planned interfaces
and [delivery sequence](roadmap.md#anl-os-delivery-track-planned). The current
hosted compiler supplies no freestanding entry, hardware intrinsics or OS
implementation. No OS target architecture or ISA has been selected.

## Current stage coverage

The following evidence covers immutable revision `m1-2026-11-16` and the separate
`local-state-2026-11-17` and `flat-products-2026-11-17` extensions. It records implemented slices rather than
completion of the broader requirement IDs. All 52
technical requirements remain in the tables below, including missing features.

| Requirement slices | Current evidence | Remaining scope |
| --- | --- | --- |
| L01, L02, L03 (flat tuples), L09, C01 | Rust checks and interprets `i64`, `bool`, unit, flat tuples of 1–8 scalar fields, immutable and initialized mutable bindings, assignment, while loops, blocks, conditionals, operators, and recursive functions; [tuple rules](../spec/flat-products.md) define bounded shapes and value snapshots. [Local-state rules](../spec/control-flow.md) and [tests](../tests/control_flow.rs) cover permissions, scope, effects, traps, and sequencing. | Wider types/inference, nested tuples, arrays, slices, records, collections, references, early return, break/continue, and the other language features remain open. |
| L06, C01 | [File modules](modules.md) provide private/public declarations, qualified paths, bounded graph loading, and cross-file diagnostics; [module tests](../tests/modules.rs) exercise checking and native execution. | Packages, import aliases, separate compilation, explicit errors and propagation, and broader interfaces remain open. |
| C02, C03 | Validated structured MIR and a [C11 native backend](native-compilation.md) build and run scalar and flat-tuple programs; [native tests](../tests/native.rs) compare results and traps at `-O0` and `-O2`. | Ownership/effects, verified-build enforcement, optimization passes, source debugging, and broader target/runtime support remain open. |
| F01, F02 | [Inventoried Lean theorems](../formal/PROOFS.md) discharge FM-01 through FM-05 for the documented v0 model. The separate LocalState model proves typing, progress/preservation, finite run/reduction correspondence, and forward finite v0 outcome preservation. The [flat-tuple model](../formal/PROOFS.md#flat-scalar-products-with-local-state) separately proves inference equivalence, typed finite machine safety, finite run/step correspondence and forward finite LocalState embedding. | No termination, reverse divergence, or equal-resource-budget claim. Rust/JSON/native correspondence, heap ownership, and concurrency proofs remain open. |
| F03, F05 | [Contract verification](verification.md) checks every function in a scalar or flat-tuple graph with mutable locals, annotated loops and acyclic calls for ordered precondition definedness, satisfiability, arithmetic safety, invariant initialization/preservation, and postconditions using Z3 5.3.3; reports bind exact inputs and distinguish failed, unknown, unsupported, and error outcomes. Ordinary compilation name/type-checks and erases annotations; verification separately checks their truth and definedness. | Results are `smt-trusted`; models are unreplayed. Assertions, recursive verification, refinements, heap properties, and checked solver certificates remain open. |
| F06, F07 | The [merged product generator](../formal/PROOFS.md#merged-flat-tuple-contract-verification) proves actual-machine safety at every budget, normal-result/environment coverage, ordered entry definedness, typed entry witnesses and exact contract-query acceptance under successful generation, typing, representation/support and valid-check premises. Lean also proves call-free, finite body-expansion, and loop-free state-verification soundness. The concrete invariant-loop generator adds actual-machine safety at every budget, normal-outcome coverage, typed nonvacuous entry contracts, and exact mathematical check partition, under successful generation and the documented typing, support, representation and logical-validity premises. Separately, the [generation-height theorem](../formal/PROOFS.md#sufficient-generation-height-with-a-supplied-call-rank) gives an explicit uniform height for the actual invariant model from verification-ready typing, typed precondition metadata, a supplied decreasing call rank and input environment length, for arbitrary symbolic contents, path and fresh counter. | FM-07 remains partial: rank existence/extraction and source call-graph correspondence, fixed production budgets, separate AST-inlining equivalence, production named-condition correspondence, and Rust/SMT/solver bridges remain open, including correspondence between formal state generators and production merged flows. Production invariant-loop and product results remain solver-trusted. Product generation completeness, solver completeness and production-bound sufficiency remain open; no termination or native-correctness claim follows. |
| F06, F07, C05 | Validated v0/v1 [core interchange](../spec/core-format.md), Rust and Lean evaluators, malformed-input tests and executable comparisons. The actual Lean [v2 reader](../formal/README.md#v2-interchange-adapter) has machine-checked acceptance soundness: successful decoding yields a typed input; execution excludes invalid outcomes and preserves returned types at every budget. V2 resource-boundary comparisons remain inconclusive. | JSON-text interpretation, compiled reader execution, compiler/model correspondence, module lowering, transformation and native-backend proof obligations remain open. No per-artifact kernel certificate is supplied. |
| T01, DOC01, DOC02 | Working `check`, `eval`, `build`, `run`, `emit-c`, `verify`, `dump-core`, and `eval-core` commands, [getting started](getting-started.md), examples, and contributor/proof instructions. | Packages, editor tools, broader verification, and complete learning/reference material remain open. |
| Q01 (development checks) | [CI](../.github/workflows/ci.yml) runs pinned Rust checks and Lean proof/comparison checks. The Linux/macOS Rust jobs and the Lean proof/comparison job, including loop-free mutable-code verification and the 166-statement inventory, passed at `088c9b793aff4afa499981ebddc7af2dda33b944` ([run](https://github.com/djsydney04/ANL/actions/runs/44071284677)); that run precedes source loop annotations. | Fuzzing, security, clean installation, and release qualification remain open. |

There is no source-level I/O, ownership, concurrency, or qualified installable
release. Contract verification supports scalar and flat-tuple code with
annotated loops and acyclic calls; see the [flat-tuple specification](../spec/flat-products.md).
Nested aggregates and recursive verification remain open. The [roadmap](roadmap.md) retains these
requirements and the full-language acceptance criteria.

## Language and execution

Entries below describe the required complete capabilities. The stage coverage
above is partial; unimplemented portions remain **planned**. The milestone column
identifies an initial delivery target. Later milestones remain required for the
complete language.

| ID | Required capabilities | Target milestone | Required evidence |
| --- | --- | --- | --- |
| L01 | Strong static typing, sound inference, rejection of invalid operations, explicit conversions | M1–M4 | Normative judgments, negative cases, inference conformance, scoped soundness proofs |
| L02 | Numeric, boolean, character, string types | M1–M4 | Boundary/literal/encoding tests and documented arithmetic semantics |
| L03 | Arrays, slices, tuples, records, collections | M4 | Construction, access, bounds, layout and lifetime tests |
| L04 | ADTs, tagged unions, exhaustive patterns | M4 | Exhaustiveness algorithm, rejection tests, lowering conformance |
| L05 | Generic functions/data, higher-order functions, closures, functional abstractions | M4 | Instantiation/inference tests, captured-resource tests, real generic data structure |
| L06 | Module/interface boundaries, explicit errors and propagation | M2–M4 | Multi-module binaries, visibility, error propagation and ABI tests |
| L07 | Mutability, aliasing, stack/heap ownership, resource lifetimes, borrowing, safe cleanup | M4 | Negative lifetime/alias tests, memory model, cleanup tests, safety coverage ledger |
| L08 | HM, bidirectional, parametric polymorphism, traits, linear/affine, regions/lifetimes, refinements, dependent types, effects, capabilities, typestate, sessions, higher-kinded types evaluated | M0 | Comparison with soundness, expression, complexity, inference, verification, compile/runtime performance and usability consequences |
| L09 | Pure functions, recursion, immutable bindings, mutable state, loops and structured control flow | M1–M4 | Evaluation-order and trap tests, state/loop semantics, recursive programs |
| L10 | Explicit unsafe, layout, pointers, buffers, native interoperability; GC not mandatory | M4 | Unsafe contracts, layout tests, C ABI programs, sanitizer/security review |
| L11 | Native threads, async, futures/tasks, structured scopes, channels, message passing, actors if justified | M4 | Executable concurrent examples, task lifetime and channel safety tests |
| L12 | Synchronization, atomics, executors, schedulers, cancellation, timeout, parallel computation | M4 | Memory model, race rejection, scheduler/cancellation stress, resource cleanup |
| L13 | Distinct guarantees for race freedom, deadlock, starvation and protocol correctness | M4 | Explicit theorem assumptions, counterexamples to guarantees not provided |
| L14 | OS/files/network/process/thread access, binary data, serialization, native linking/platform operations | M4 | CLI, network server, process and FFI examples on supported platforms |

## Formal methods and compiler

| ID | Required capabilities | Target milestone | Required evidence |
| --- | --- | --- | --- |
| F01 | Grammar, judgments, operational, memory, ownership, effects, error and concurrency semantics | M1–M4 | Versioned formal model corresponding to implemented features |
| F02 | Mechanized soundness for defined core, scope distinguished from whole implementation | M1 onward | Pinned checker logs, theorem statements, absence of admitted target theorems, bridge limitations |
| F03 | Preconditions, postconditions, invariants, loop invariants, assertions, refinements | M3–M4 | VC generator plus positive, false and unknown examples including overflow |
| F04 | Ghost/proof-only code, state transitions, protocol contracts, data-structure properties | M3–M5 | Erasure rules, specification soundness tests, machine-checked examples |
| F05 | Type-checked, verified, dynamic, tested, unverified, failed, unknown/timeout distinguished | M3 | CLI statuses and artifacts; missing solver, crash and timeout fail-closed tests |
| F06 | IR semantics, transformation proofs, lowering preservation, validation, verified subsets, checkable artifacts | M2 onward | Pass-specific proof/validation evidence and pipeline coverage matrix |
| F07 | Differential/property tests complement proof; explicit backend, parser, type checker, VCG, solver, runtime, unsafe, FFI and OS trust | every phase | Independent reference comparisons and maintained trust ledger |
| C01 | Lexer/parser/AST, name/module resolution, inference/checking, diagnostics | M1–M2 | Positive and negative source tests with source locations |
| C02 | Ownership/effect analyses, verification integration, validated IRs, lowering, optimization, debug info | M2–M4 | IR validators, pass invariants, semantic comparison and debugger sessions |
| C03 | Native code generation, linking, executable programs | M2 | Build and run real native binaries, inspect platform format, compare model outcomes |
| C04 | LLVM, MLIR, Cranelift and relevant alternatives evaluated | M0 | Sourced backend tradeoff record and selected strategy |
| C05 | Independent reference interpreter or executable formal model | M1 | Model comparison, divergent mutations caught, call/trap semantics |
| C06 | Folding, inlining, dead-code/escape/loop/allocation analysis, specialization, layout, interprocedural/LTO evaluated | M4–M6 | Optimization decision records and semantic preservation regression tests |
| C07 | Compile time, runtime, binary size, memory and verification latency against C/Rust/C++/OCaml where suitable | M6 | Reproducible benchmark sources, environment, raw measurements and honest regressions |

## Runtime, library and agents

| ID | Required capabilities | Target milestone | Required evidence |
| --- | --- | --- | --- |
| R01 | Initialization, allocation, resources, errors/panics, I/O, OS/FFI | M2–M4 | ABI and lifecycle tests, documented mandatory/optional components |
| R02 | Concurrency, async, observability, agent workflow support | M4–M5 | Real applications, traces, failure and cancellation tests |
| S01 | Primitive utilities, text, strings, collections, iterators | M4 | Documented public APIs, property/boundary tests, examples |
| S02 | Filesystem, paths, I/O, networking, time, processes | M4 | Platform tests and external-developer examples |
| S03 | Concurrency, synchronization, async and errors | M4 | Resource/race and error recovery tests |
| S04 | Formatting, parsing, serialization, tests, logging/tracing | M4–M6 | Compatibility corpus, malformed-input tests, generated API docs |
| S05 | Safe wrappers for established cryptography | M4–M7 | Audited FFI/provider boundaries, known-answer tests, no invented cryptography |
| A01 | Typed interfaces/tools, local state, communication, workflows, parallelism, capabilities | M5 | Typed agents, rejection of missing authority, protocol and state tests |
| A02 | Durable execution/recovery, retries, cancellation/timeouts, traces, deterministic replay | M5 | Crash injection, replay with recorded nondeterminism, duplicate-effect policy |
| A03 | State-machine/protocol verification, budgets, human approval, test environments | M5 | Protected-state proofs, adversarial capability tests, budget enforcement, simulated tools |
| A04 | External model correctness remains an assumption; libraries preferred over special syntax | M0–M5 | Trust documentation, deterministic core separated from external responses |

## Ecosystem and final release

| ID | Required capabilities | Target milestone | Required evidence |
| --- | --- | --- | --- |
| T01 | Coherent CLI, scaffolding/build/run/check/verify/test/fmt/lint/doc/dependency/version workflows | M1–M6 | Actual CLI user journeys; unsupported commands cannot claim success |
| T02 | Package management, dependency resolution and reproducible builds | M6 | Locked transitive graph, clean offline/cache builds, hash and conflict failures |
| T03 | Formatter, linter, test runner, documentation generator | M6 | Formatting stability/semantics, actionable lint, real tests, linked API docs |
| T04 | Language server, diagnostics, completion, debugger and editor integration | M6 | LSP protocol tests, editor and native-debugger exercises |
| D01 | Supported-platform install, versioned binaries, integrity, upgrades/uninstall; signing where supported | M7 | Clean-environment install from release artifacts, checksums, tamper failures, uninstall tests |
| D02 | Ordinary users need no internal compiler development dependencies | M7 | Independent onboarding with only published prerequisites |
| DOC01 | Book, examples, language reference, standard-library reference, verification guide | M1–M7 | Working examples, full implemented-feature coverage and searchable API docs |
| DOC02 | Compiler internals, agent, install, contributor, migration/interoperability guides | M1–M7 | Navigation, versioned docs, beginner walkthroughs, runnable interoperability examples |
| W01 | Technical whitepaper covering abstract, introduction, related work, language design, typing, semantics, verification, compiler architecture/correctness, memory/concurrency, agents, performance, developer experience, limitations, conclusion, references and appendices | M7 | Versioned source and rendered professionally typeset PDF, reviewed claims and references |
| W02 | Actual results, metatheory, implementation/proof coverage, comparisons, limitations, reproducibility | M7 | Claim-to-evidence table, raw benchmark data, proof references, independent technical review |
| Q01 | CI builds, unit/integration/e2e/conformance/type/proof/verifier checks, fuzzing, static/security/performance/cross-platform/docs/install/release checks | all phases | Passing exact-revision checks whose coverage matches the capability |
| Q02 | Final audit of all requirements, limits, defects, risks, supported platforms and release blockers | M7 | Requirement-by-requirement audit with no missing mandatory evidence |
| Q03 | Independent developers install, learn, build generic/concurrent/network/agent programs, verify, use dependencies and interpret errors | M7 | Independent onboarding records using only published materials; resolved usability defects |
## Release acceptance

Every required capability needs evidence that exercises its promised behavior and
documents its assumptions. A passing subset cannot establish complete-language
support. Deferred capabilities remain open until implemented and validated.

Reproducible builds, source review, clear subsystem contracts, security evaluation,
regression checks, and versioned specifications accompany each release. Any
change to semantics must update the corresponding model, proof obligations,
compiler behavior, conformance tests and documentation.

The final audit covers the complete language, compiler, verification system,
runtime, standard library, agent libraries, tooling, installation, documentation
and whitepaper. It records unsupported features, known defects, security risks,
performance limitations and supported platforms. Release-blocking gaps must be
resolved before completion is claimed.

The audit also covers the complete ANL-authored operating system and the
[OS authorship and expressibility gate](#os-authorship-and-expressibility-gate).
All 52 technical requirements and this cross-cutting gate remain open.
