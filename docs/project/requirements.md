# Requirements and acceptance evidence

The [founding charter](founding-charter.txt) is the complete source of requirements.
This ledger groups them for ownership and verification; it does not remove any
charter clause. Final qualification must check each item within each group.

Status words have narrow meanings. **Planned** has no implemented evidence.
**Designed** has an accepted specification. **Implemented** has executable code.
**Tested** has named passing checks. **Machine-checked** names the theorem, model,
tool version, and assumptions. **Released** requires installed release artifacts.
One status never implies another. A milestone does not imply final release.

## Phase 0 gate

| ID | Deliverable or predicate | Evidence location | Status |
| --- | --- | --- | --- |
| P0-01 | Unabridged founding charter | `docs/project/founding-charter.txt` | Recorded |
| P0-02 | Organization, seven research teams, bounded assignments | `docs/project/organization.md` | Research assigned; review pending |
| P0-03 | Competing architectural research with primary sources | `docs/research/` | In progress |
| P0-04 | Integrated overview covering all §25.3 topics and diagrams | `docs/architecture/overview.md` | Planned |
| P0-05 | Language requirements and final acceptance mapping | This document and charter | Recorded; no functionality inferred |
| P0-06 | Formal-methods strategy and trust boundaries | `docs/architecture/formal-methods.md`, `trust.md` | In progress |
| P0-07 | Type-system specification and memory decisions | `docs/architecture/type-system.md`, `runtime.md` | In progress |
| P0-08 | Compiler and IR specification | `docs/architecture/compiler.md` | In progress |
| P0-09 | Runtime architecture | `docs/architecture/runtime.md` | In progress |
| P0-10 | Agent architecture | `docs/architecture/agents.md` | In progress |
| P0-11 | Initial grammar proposal | `spec/grammar.ebnf` | In progress |
| P0-12 | Decision records and competing alternatives | `docs/architecture/decisions.md` | Planned |
| P0-13 | Ownership, dependencies, executable roadmap, acceptance criteria | `organization.md`, `roadmap.md` | Recorded |
| P0-14 | Research bibliography | `docs/research/bibliography.md` | Planned |
| P0-15 | Initial CI and contribution strategy | `CONTRIBUTING.md` | Recorded; CI execution pending |
| P0-16 | Independent critique and resolution of blocking findings | `docs/research/independent-review.md` | Planned |
| P0-17 | Compatible formal/compiler contracts acknowledged by teams | `docs/architecture/contracts.md` | Planned |
| P0-18 | Artifacts committed to GitHub, reviewed and accepted by Astra | `docs/project/phase-0-acceptance.md` | Pending |

## Language and execution

All entries below are **planned**, unless an evidence record explicitly updates
the entry. The phase column assigns an initial delivery gate, not permission to
omit a requirement from the final product.

| ID | Charter | Required capabilities | Owner / phase | Required evidence |
| --- | --- | --- | --- | --- |
| L01 | §1–3 | Strong static typing, sound inference, rejection of invalid operations, explicit conversions | Language / M1–M4 | Normative judgments, negative cases, inference conformance, scoped soundness proofs |
| L02 | §3 | Numeric, boolean, character, string types | Language / M1–M4 | Boundary/literal/encoding tests and documented arithmetic semantics |
| L03 | §3 | Arrays, slices, tuples, records, collections | Language + library / M4 | Construction, access, bounds, layout and lifetime tests |
| L04 | §3,5 | ADTs, tagged unions, exhaustive patterns | Language / M4 | Exhaustiveness algorithm, rejection tests, lowering conformance |
| L05 | §3,5 | Generic functions/data, higher-order functions, closures, functional abstractions | Language / M4 | Instantiation/inference tests, captured-resource tests, real generic data structure |
| L06 | §3 | Module/interface boundaries, explicit errors and propagation | Compiler / M2–M4 | Multi-module binaries, visibility, error propagation and ABI tests |
| L07 | §3–5 | Mutability, aliasing, stack/heap ownership, resource lifetimes, borrowing, safe cleanup | Language + runtime / M4 | Negative lifetime/alias tests, memory model, cleanup tests, safety coverage ledger |
| L08 | §3 | HM, bidirectional, parametric polymorphism, traits, linear/affine, regions/lifetimes, refinements, dependent types, effects, capabilities, typestate, sessions, higher-kinded types evaluated | Language / M0 | Comparison with soundness, expression, complexity, inference, verification, compile/runtime performance and usability consequences |
| L09 | §5 | Pure functions, recursion, immutable bindings, mutable state, loops and structured control flow | Language / M1–M4 | Evaluation-order and trap tests, state/loop semantics, recursive programs |
| L10 | §4,7 | Explicit unsafe, layout, pointers, buffers, native interoperability; GC not mandatory | Systems / M4 | Unsafe contracts, layout tests, C ABI programs, sanitizer/security review |
| L11 | §6 | Native threads, async, futures/tasks, structured scopes, channels, message passing, actors if justified | Systems / M4 | Executable concurrent examples, task lifetime and channel safety tests |
| L12 | §6 | Synchronization, atomics, executors, schedulers, cancellation, timeout, parallel computation | Systems / M4 | Memory model, race rejection, scheduler/cancellation stress, resource cleanup |
| L13 | §6 | Distinct guarantees for race freedom, deadlock, starvation and protocol correctness | Formal + systems / M4 | Explicit theorem assumptions, counterexamples to guarantees not provided |
| L14 | §7 | OS/files/network/process/thread access, binary data, serialization, native linking/platform operations | Systems / M4 | CLI, network server, process and FFI examples on supported platforms |

## Formal methods and compiler

| ID | Charter | Required capabilities | Owner / phase | Required evidence |
| --- | --- | --- | --- | --- |
| F01 | §9–10 | Grammar, judgments, operational, memory, ownership, effects, error and concurrency semantics | Formal / M1–M4 | Versioned formal model corresponding to implemented features |
| F02 | §3,10 | Mechanized soundness for defined core, scope distinguished from whole implementation | Formal / M1 onward | Pinned checker logs, theorem statements, absence of admitted target theorems, bridge limitations |
| F03 | §11 | Preconditions, postconditions, invariants, loop invariants, assertions, refinements | Verification / M3–M4 | VC generator plus positive, false and unknown examples including overflow |
| F04 | §11 | Ghost/proof-only code, state transitions, protocol contracts, data-structure properties | Verification / M3–M5 | Erasure rules, specification soundness tests, machine-checked examples |
| F05 | §11 | Type-checked, verified, dynamic, tested, unverified, failed, unknown/timeout distinguished | Verification / M3 | CLI statuses and artifacts; missing solver, crash and timeout fail-closed tests |
| F06 | §12 | IR semantics, transformation proofs, lowering preservation, validation, verified subsets, checkable artifacts | Formal + compiler / M2 onward | Pass-specific proof/validation evidence and pipeline coverage matrix |
| F07 | §12–13 | Differential/property tests complement proof; explicit backend, parser, type checker, VCG, solver, runtime, unsafe, FFI and OS trust | Quality + formal / every phase | Independent reference comparisons and maintained trust ledger |
| C01 | §14 | Lexer/parser/AST, name/module resolution, inference/checking, diagnostics | Compiler / M1–M2 | Positive and negative source tests with source locations |
| C02 | §14–15 | Ownership/effect analyses, verification integration, validated IRs, lowering, optimization, debug info | Compiler / M2–M4 | IR validators, pass invariants, semantic comparison and debugger sessions |
| C03 | §14 | Native code generation, linking, executable programs | Compiler / M2 | Build and run real native binaries, inspect platform format, compare model outcomes |
| C04 | §14 | LLVM, MLIR, Cranelift and relevant alternatives evaluated | Compiler / M0 | Sourced backend tradeoff record and selected strategy |
| C05 | §14 | Independent reference interpreter or executable formal model | Formal + compiler / M1 | Model comparison, divergent mutations caught, call/trap semantics |
| C06 | §16 | Folding, inlining, dead-code/escape/loop/allocation analysis, specialization, layout, interprocedural/LTO evaluated | Compiler / M4–M6 | Optimization decision records and semantic preservation regression tests |
| C07 | §16 | Compile time, runtime, binary size, memory and verification latency against C/Rust/C++/OCaml where suitable | Quality / M6 | Reproducible benchmark sources, environment, raw measurements and honest regressions |

## Runtime, library and agents

| ID | Charter | Required capabilities | Owner / phase | Required evidence |
| --- | --- | --- | --- | --- |
| R01 | §17 | Initialization, allocation, resources, errors/panics, I/O, OS/FFI | Runtime / M2–M4 | ABI and lifecycle tests, documented mandatory/optional components |
| R02 | §17 | Concurrency, async, observability, agent workflow support | Runtime / M4–M5 | Real applications, traces, failure and cancellation tests |
| S01 | §18 | Primitive utilities, text, strings, collections, iterators | Library / M4 | Documented public APIs, property/boundary tests, examples |
| S02 | §18 | Filesystem, paths, I/O, networking, time, processes | Library / M4 | Platform tests and external-developer examples |
| S03 | §18 | Concurrency, synchronization, async and errors | Library / M4 | Resource/race and error recovery tests |
| S04 | §18 | Formatting, parsing, serialization, tests, logging/tracing | Library / M4–M6 | Compatibility corpus, malformed-input tests, generated API docs |
| S05 | §18 | Safe wrappers for established cryptography | Library + security / M4–M7 | Audited FFI/provider boundaries, known-answer tests, no invented cryptography |
| A01 | §8,30 | Typed interfaces/tools, local state, communication, workflows, parallelism, capabilities | Agents / M5 | Typed agents, rejection of missing authority, protocol and state tests |
| A02 | §8,30 | Durable execution/recovery, retries, cancellation/timeouts, traces, deterministic replay | Agents / M5 | Crash injection, replay with recorded nondeterminism, duplicate-effect policy |
| A03 | §8,30 | State-machine/protocol verification, budgets, human approval, test environments | Agents + formal / M5 | Protected-state proofs, adversarial capability tests, budget enforcement, simulated tools |
| A04 | §8 | External model correctness remains an assumption; libraries preferred over special syntax | Agents / M0–M5 | Trust documentation, deterministic core separated from external responses |

## Ecosystem and final release

| ID | Charter | Required capabilities | Owner / phase | Required evidence |
| --- | --- | --- | --- | --- |
| T01 | §19 | Coherent CLI, scaffolding/build/run/check/verify/test/fmt/lint/doc/dependency/version workflows | Tooling / M1–M6 | Actual CLI user journeys; unsupported commands cannot claim success |
| T02 | §19 | Package management, dependency resolution and reproducible builds | Tooling / M6 | Locked transitive graph, clean offline/cache builds, hash and conflict failures |
| T03 | §19 | Formatter, linter, test runner, documentation generator | Tooling / M6 | Formatting stability/semantics, actionable lint, real tests, linked API docs |
| T04 | §19 | Language server, diagnostics, completion, debugger and editor integration | Tooling / M6 | LSP protocol tests, editor and native-debugger exercises |
| D01 | §32.3 | Supported-platform install, versioned binaries, integrity, upgrades/uninstall; signing where supported | Distribution / M7 | Clean-environment install from release artifacts, checksums, tamper failures, uninstall tests |
| D02 | §32.3 | Ordinary users need no internal compiler development dependencies | Distribution / M7 | Independent onboarding with only published prerequisites |
| DOC01 | §32.4 | Book, examples, language reference, standard-library reference, verification guide | Publications / M1–M7 | Working examples, full implemented-feature coverage and searchable API docs |
| DOC02 | §32.4 | Compiler internals, agent, install, contributor, migration/interoperability guides | Publications / M1–M7 | Navigation, versioned docs, beginner walkthroughs, runnable interoperability examples |
| W01 | §32.2 | Complete technically rigorous whitepaper including every named section | Publications / M7 | Versioned source and rendered professionally typeset PDF, reviewed claims and references |
| W02 | §32.2 | Actual results, metatheory, implementation/proof coverage, comparisons, limitations, reproducibility | Publications + quality / M7 | Claim-to-evidence table, raw benchmark data, proof references, independent technical review |
| Q01 | §24,35,42 | CI builds, unit/integration/e2e/conformance/type/proof/verifier checks, fuzzing, static/security/performance/cross-platform/docs/install/release checks | Quality / all phases | Passing exact-revision checks whose coverage matches the capability |
| Q02 | §32.1,44 | Final audit of all requirements, limits, defects, risks, supported platforms and release blockers | Quality / M7 | Requirement-by-requirement audit with no missing mandatory evidence |
| Q03 | §32.5 | Independent developers install, learn, build generic/concurrent/network/agent programs, verify, use dependencies and interpret errors | Independent reviewers / M7 | Fresh-context onboarding records using only published materials; resolved usability defects |
| G01 | §20–25,33–43 | Organization, decomposition, review, ownership, governance, incremental commits, roadmap, persistent memory, continued execution | Coordinator / all phases | Live assignments, integrated commits, reviews, evidence and exact handoff records |

## Completion policy

The release gate is the conjunction of all mandatory capabilities, not a count of
green tests or files. A capability is accepted only when its evidence exercises
the promised behavior and documents relevant assumptions. Deferred work remains
open in this ledger. Revisions to the architecture cannot silently narrow the
charter. Final audits must re-read the charter as well as this map.
