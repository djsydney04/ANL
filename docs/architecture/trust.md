# Trust boundaries and guarantee ledger

Status: evidence ledger for immutable scalar revision `m1-2026-11-16` and the
separate local-state, flat-tuple and `anl-owned-buffers-v1` extensions, with the wider language still planned. Rust source checking, interpretation, modules,
native compilation, local scalar state and loops, scalar and flat-tuple contract
verification with invariants and acyclic calls, and strict v0/v1 interchange have executable
conformance coverage. Lean's expression and recursive-function models have kernel-checked
theorems, including finite evaluator correspondence with sufficient depth and
fuel. The local-state model has separate initialized-cell typing, current-state
machine safety, finite run/reduction correspondence, and forward finite v0 outcome
preservation. Verification-condition proofs include loop-free local-state updates,
finite body expansion and callee preconditions when generation succeeds. The
concrete invariant-loop model connects valid generated checks to safety of actual
machine runs at every budget and coverage of finite normal returns, including
typed entry contracts and exact mathematical check partition. A separate
supplied-rank theorem establishes a uniform height for actual model generation
from verification-ready typing, typed preconditions and input environment length,
independently of symbolic contents, path and initial fresh counter. The production
verifier supports annotated loops and remains `smt-trusted`. Rust and
source/module/backend correctness proofs and a qualified release remain open.
Architecture review alone cannot change a component to verified.

Current evidence is available in the [source conformance tests](../../tests/conformance.rs),
[API and I/O boundary tests](../../tests/boundaries.rs),
[native tests](../../tests/native.rs), [module tests](../../tests/modules.rs),
[contract tests](../../tests/contracts.rs), [verifier tests](../../tests/verification.rs),
[local-state tests](../../tests/control_flow.rs),
[state-verifier tests](../../tests/state_verification.rs),
[formal build and comparison instructions](../../formal/README.md), and
[theorem inventory](../../formal/PROOFS.md). The inventory names the exact theorem
statements, Lean 4.36.0 toolchain, axiom dependencies, and remaining obligations.
Local validation is separate from configured cross-platform CI and release
qualification.

Flat tuples additionally have executable source, interpreter, v2 interchange
and native support under their [own contract](../../spec/flat-products.md).
Their separate runtime model proves inference equivalence, typed finite-trace
safety, finite run/step correspondence and forward finite LocalState embedding.
The [v2 adapter](../../formal/README.md#v2-interchange-adapter) has a proved
acceptance boundary. Successful decoding implies a typed expression or a
well-typed complete function table with a nullary i64 entry. Its model execution
excludes invalid outcomes and preserves returned types at every budget. JSON-text
interpretation, Lean compilation/runtime and Rust/native correspondence remain
unproved; executable comparisons cover those boundaries only for tested cases.
`verify` supports flat-tuple contracts with annotated loops and acyclic calls.
Those results remain `smt-trusted`. Runtime type safety alone does not establish
contract verification. The [merged product model](../../formal/PROOFS.md#merged-flat-tuple-contract-verification)
separately proves actual-machine safety and normal ensures under successful
generation, typing, representation/support and valid-check premises. Its ordered
entry and exact query results retain typed runtime witnesses and check multiplicity.
No result certifies Rust generation, source annotation or ID reconstruction,
SMT/solver answers or native execution. Product generation completeness, solver
completeness, production-bound sufficiency and termination remain open.

The [owned-buffer model](../../formal/PROOFS.md#owned-buffers-and-coremir-correspondence)
adds raw syntax and independent typing, finite heap and capability safety,
read-loan preservation, source-site provenance, normal cleanup and a separate
resource-accounted reference wrapper. Canonical model Core/MIR lowering has finite
completed correspondence in both directions under the same allocator responses,
including exact world and current/suspended capability state. Actual `Pair.check`
and `Wire.checkDocuments` acceptance supply that relationship. Their strict
readers validate every function, annotation, identity and profile; byte/JSON
interpretation and compiled execution remain trust boundaries.

The reference corpus covers 53 cases: 18 values, 8 traps, 7 resource-limited
prefixes and 20 rejections. It complements earlier production/native captures;
it is finite comparison evidence, not a universal compiler theorem. Administrative
exhaustion, infrastructure failures and missing/malformed reports are incomplete.
No proof equates Core/MIR transition budgets, resource cutoffs or exhausted states.
No new native performance claim follows from this evidence. Heap contract
verification remains explicitly unsupported with exit 7.

## What a claim covers

Every claim records the program or formal artifact, property, semantic revision, supported feature subset, platform, toolchain, assumptions, and evidence method. Type checking, testing, runtime checking, solver discharge, kernel proof, and translation validation remain distinct. A guarantee about one layer does not automatically extend to another layer.

For example, a Lean theorem establishing scalar preservation applies to the formal transition relation and the stated typing judgment. It does not prove the Rust parser implements that judgment, the C emitter preserves traps, or an OS executes a binary correctly. Each connection needs its own evidence.

## Trusted components and current evidence

| Component | What depends on it | Current evidence and required strengthening |
| --- | --- | --- |
| Language definitions and theorem statements | Whether checked mathematics describes intended ANL behavior | Independent technical review, semantic examples, and implementation correspondence tests. Formalizing the wrong statement remains possible. |
| Lean kernel and allowed logical axioms | Kernel-checked theorem validity | Lean 4.36.0 is pinned; the earlier APL inventory has 558 named theorem audits and 72 separate module replays. The additional memory package has 72 ANL source modules with an all-declaration audit and separate-process kernel replay. The public check scripts retain both scopes; counts are not whole-language proof measures. Actual dependencies and theorem scopes are recorded in the inventory. Counts include supporting lemmas. Hardware and host integrity remain assumptions. |
| Lean elaboration and proof libraries | Meaning of the submitted statement and imported definitions | Review notation, theorem inventory, dependencies, and changes. Axiom inspection alone does not establish the intended meaning. |
| Formal evaluator compilation and JSON reader | Executed reference results | V0 finite evaluator correspondence quantifies sufficient depth/fuel. The separate v1 machine has finite run/reduction correspondence and forward v0 outcome preservation. The flat-tuple machine has finite run/step correspondence and forward finite v1 embedding under its stated premises. Typed model runs cannot reach invalid. The actual v2 reader's successful return supplies the typing premise, and its execution wrapper preserves that guarantee at every budget. V1/v2 transition budgets differ from Rust expression/depth/allocation/slot limits; resource comparisons are inconclusive. JSON-text interpretation, v0/v1 reader correspondence, Lean compilation and runtime remain trusted or tested boundaries. No per-artifact kernel certificate is produced. |
| Source lexer, parser, resolver, and elaborator | Correspondence between user source and formal core | Implemented and tested for scalar programs, file modules, and initialized local state, including scope, permissions, visibility, numeric boundaries, retained source locations, and serialized core comparisons. Module resolution and source elaboration remain correspondence obligations. |
| Production type checker | Rejection of ill-typed source programs | Implemented and tested for M1; checked Program contents cannot be constructed or mutated through the safe public Rust API. The abstract typing relation and Lean inference theorems do not prove this checker sound. |
| Ownership and effect checkers | Memory safety, race prevention, and capability restrictions | Owner/read/edit checks are implemented for scoped buffers with one call-scoped view. Independent model safety and actual-artifact pair validation cover the documented subset. Production checker correctness, general moves/escaping borrows, effects and concurrency remain open. |
| Verification IR construction and VCG | Whether a discharged formula implies the requested source property | The Rust verifier supports scalar and flat-tuple functions with mutable locals, annotated loops and acyclic calls; it rejects missing invariants and recursion before tools run. Lean proves call-free, finite body-expansion, loop-free state, and invariant-loop generator soundness under successful generation and the documented premises. The loop model includes actual-machine safety, normal coverage, typed entry contracts and exact mathematical query partition. Separately, verification-ready typing, typed preconditions, a supplied decreasing call rank and input environment length imply a uniform generation height for the actual model. Rank existence/extraction, source graph correspondence, fixed production limits, separate AST-inlining equivalence, production named-condition correspondence, and production bridges remain open (partial FM-07). |
| SMT serializer, solver, and result parser | Solver-backed proof results and counterexamples | Z3 5.3.3 is pinned. The driver records exact tool/query hashes, bounds time and I/O, validates status/models, and requires successful process termination. Real-solver and failure-protocol tests passed in Linux/macOS CI at `a7e0b38591ba76255e561cda60099bc8bc422543` ([run](https://github.com/djsydney04/ANL/actions/runs/44051779446)). Results remain `smt-trusted`; models are unreplayed and no certificate checker is implemented. |
| Compiler transformations | Preservation of values, traps, effects, and divergence properties | Source blocks and modules lower to a typed function table, then validated structured MIR with initialized scalar slots and loops. Tests cover scope, ordering, state changes, branches, and traps. A separate formal canonical memory lowerer has finite completed Core/MIR correspondence in both directions, and successful pair validation connects actual artifacts to it. This does not prove the Rust implementation or source/module lowering. ANL optimization passes remain unimplemented. |
| C or LLVM backend, assembler, and linker | Machine code correctness | The C11 backend is implemented and tested at `-O0`/`-O2`, including checked arithmetic and sanitizer probes. Native and module checks passed macOS AArch64 and Linux x86-64 CI at `19d726c`; compiler, linker, and host behavior remain trusted. LLVM is planned. |
| Runtime and allocator | Cleanup, layout, I/O, concurrency, and memory safety | Scalar arithmetic/trap/output helpers are implemented and tested. Interpreter tuple storage and reclamation depend on Rust and its allocator and are outside the mathematical runtime model. Scoped `i64` owners, call views and normal cleanup are implemented, with a separate finite heap/capability model. The hosted C allocator, Rust backing and native execution remain trusted; no host allocation-success or physical-memory bound is proved. General owned APIs, source I/O, concurrency and ANL OS memory management remain open. |
| Unsafe ANL and foreign libraries | Any safe abstraction that depends on them | Explicit contracts, versioned dependencies, and reviewed wrappers. Foreign violations can invalidate dependent safety claims. |
| OS and hardware | Execution, scheduling, memory, I/O, and clock assumptions | Explicit platform support and integration tests. A language proof does not verify these components. |
| Package resolution and distribution | Which code and proofs are actually consumed | Locked content hashes, reproducible inputs, provenance, artifact integrity, and clean installation tests. |
| External tools and model providers | Agent observations and effects | Treat responses as untrusted inputs constrained by contracts. No semantic truth guarantee for model-generated content. |

The baseline scope follows the distinction in Lean's proof-validation guidance and CompCert's published compiler theorem boundary. [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/), [CompCert theorem scope](https://compcert.org/man/manual001.html).

## Acceptable evidence labels

`designed` means an accepted specification exists. `implemented` means reachable code exists. `tested` means named tests passed for identified inputs. `type-checked` means the checker accepted a program under a stated language version. `dynamically-checked` describes runtime enforcement on actual executions. `solver-verified` means the supported obligation was discharged under the recorded solver and encoding assumptions. `kernel-checked` identifies an actual theorem and its audited dependencies. `translation-validated` identifies a particular compilation and a validator whose soundness scope is recorded.

Do not collapse these labels into a generic green check. The named Lean
expression and recursive-function theorems discharge FM-01 through FM-05 for that
model. Completeness requires sufficient depth and fuel; it does not prove
termination or completeness at fixed CLI limits. Rust/model correspondence proofs
(FM-06) remain open. FM-08 now has the scoped canonical memory lowering result
above; production/optimization/native lowering remains open. The separate local-state proofs
cover their typed machine and forward finite v0 embedding; they do not prove
reverse divergence correspondence or identical production resource limits.
FM-07 includes sound finite body expansion with callee preconditions,
loop-free local-state updates and the concrete invariant-loop generator when
generation succeeds. The loop theorem requires typed represented inputs on a true
input path, bounded input symbols/path and checks valid in every model extension preserving earlier
symbols. It connects to actual `LocalState.run` and `Steps`, excludes finite traps
and invalid states, and covers normal returns with their final environments.
It asserts neither termination nor a returning budget.

The contract wrapper preserves original declaration-order parameter values and
requires ordered definedness on every typed input, a typed satisfying input,
and universally valid body/post checks for satisfying inputs. Its safety and
postcondition theorems also require successful generation and verification-ready
annotated function/body typing. The query theorem
preserves every original guarded check under mathematical tagging and grouping.
Neither result proves production naming, source metadata or query generation.
The separate [generation-height result](../../formal/PROOFS.md#sufficient-generation-height-with-a-supplied-call-rank)
uses result-free static `PreType` metadata and a supplied rank covering every
syntactic call, including calls in arguments, conditions and source-dead code.
Its explicit height works for every symbolic environment of the required length,
every path and every fresh counter, preserving output environment length. It asserts
neither truth nor definedness of specifications. Siblings reuse child height;
finite model generation gives no implementation work/memory bound, fixed-budget
completeness, logical acceptance or runtime termination claim.

Rank existence/extraction from an acyclic graph, source call-graph checking,
separate syntax inlining, correspondence
between the formal continuation/path-split generators and Rust merged flows,
source annotation attachment, global allocation-event history, production limits,
SMT translation, solver answers and countermodel decoding remain unproved
boundaries. Guarded head domains need not constrain inactive heads in all models;
abstract head assignments are not replayed executions. Production verification is
not kernel checked. Module visibility is checked
by Rust before flattening to scalar core; the model's function theorems do not
prove that source-level boundary.

## Proof integrity policy

Foundational proofs must be rebuilt from reviewed source with the pinned proof tool. Incomplete terms, admitted statements, custom proof-bypassing axioms, disabled kernel checking, and native-evaluation trust axioms are excluded from the theorem inventory. Allowed standard logical axioms are listed explicitly in the formal strategy. Dependencies cannot hide a disallowed axiom.

The inventory maps the theorem's actual quantified statement to its advertised claim. Reviewers check that hypotheses are satisfiable and do not assume the conclusion. A theorem about the constructor `True` does not establish a property of ANL merely because its name says "compiler_correct". A proof that assumes the entire Rust checker is sound does not prove that checker sound.

Proof status is per semantic revision. Changing grammar elaboration, arithmetic, evaluation order, ownership rules, or lowering invalidates affected correspondence evidence until rechecked. A stale proof file that still builds can describe an obsolete model.

## Verification and external assumptions

The current verifier checks every loaded function and rejects recursive call
graphs and missing loop invariants before tool discovery, including unused
functions and unselected branches. Mutable state and annotated loops are supported.
A checked stateful report uses `apl-verify-v1` with verification revision
`apl-state-verify-v1` without loops or `apl-loop-verify-v1` with loops; pure programs
retain `apl-verify-v0`. A source failure has no established semantic revision and
reports null. The verifier checks callee preconditions and expands actual bodies,
without using postconditions as summaries. Ordered definedness checks prevent self-justifying
preconditions, and separate satisfiability checks reject vacuous contracts.
Ordinary compilation name/type-checks and erases contract and invariant clauses
without proving their truth or definedness or dynamically checking them. Source
annotation erasure changes no runtime core schema or semantic revision. The
[verification guide](../verification.md) explains result scope.
Future library summaries and environment assumptions must be explicit; a verified
caller cannot hide an unverified callee behind an empty contract.

External I/O, time, failures, cancellation, and foreign functions enter through modeled events. Verification can establish properties conditional on an event contract. It cannot establish that an external service honors the contract. Agent approvals must be represented by unforgeable authority in the execution model; a string saying "approved" is not authority.

A deterministic replay test confirms behavior for its recorded trace and input state. It does not prove all possible tool responses, schedules, network failures, or model outputs safe. Resource budgets require checked accounting at the actual execution boundary.

## Release claim review

Before a release, enumerate every public safety or verification claim. Link each to a theorem, validator, test, or runtime mechanism and its limits. Verify that unsupported features and targets are visible in CLI diagnostics and documentation. Inspect the actual artifacts and rerun the relevant checks.

The initial release process must include independent checks of integer overflow and division semantics, source-to-core scope handling, solver failure behavior, package integrity, unsafe interfaces, and capability boundaries when those features exist. Missing evidence blocks the corresponding claim or release requirement. It cannot be cured by describing the intended design.
