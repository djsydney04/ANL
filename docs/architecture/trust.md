# Trust boundaries and guarantee ledger

Status: evidence ledger for scalar semantic revision `m1-2026-11-16`, with the
wider language still planned. Rust source checking, interpretation, modules,
native compilation, pure acyclic contract verification, and strict core
import/export have executable conformance coverage. Lean's expression and recursive-function models have kernel-checked
theorems, including finite evaluator correspondence with sufficient depth and
fuel. A call-free verification-condition model proves contract soundness under
logical obligations; the production verifier remains `smt-trusted`. Rust and
source/module/backend correctness proofs and a qualified release remain open.
Architecture review alone cannot change a component to verified.

Current evidence is available in the [source conformance tests](../../tests/conformance.rs),
[API and I/O boundary tests](../../tests/boundaries.rs),
[native tests](../../tests/native.rs), [module tests](../../tests/modules.rs),
[contract tests](../../tests/contracts.rs), [verifier tests](../../tests/verification.rs),
[formal build and comparison instructions](../../formal/README.md), and
[theorem inventory](../../formal/PROOFS.md). The inventory names the exact theorem
statements, Lean 4.36.0 toolchain, axiom dependencies, and remaining obligations.
Local validation is separate from configured cross-platform CI and release
qualification.

## What a claim covers

Every claim records the program or formal artifact, property, semantic revision, supported feature subset, platform, toolchain, assumptions, and evidence method. Type checking, testing, runtime checking, solver discharge, kernel proof, and translation validation remain distinct. A guarantee about one layer does not automatically extend to another layer.

For example, a Lean theorem establishing scalar preservation applies to the formal transition relation and the stated typing judgment. It does not prove the Rust parser implements that judgment, the C emitter preserves traps, or an OS executes a binary correctly. Each connection needs its own evidence.

## Trusted components and current evidence

| Component | What depends on it | Current evidence and required strengthening |
| --- | --- | --- |
| Language definitions and theorem statements | Whether checked mathematics describes intended APL behavior | Independent technical review, semantic examples, and implementation correspondence tests. Formalizing the wrong statement remains possible. |
| Lean kernel and allowed logical axioms | Kernel-checked theorem validity | Lean 4.36.0 is pinned; the expression and program inventory is checked by clean builds, transitive axiom audit, and kernel replay. Actual dependencies are recorded in the inventory. Hardware and host integrity remain assumptions. |
| Lean elaboration and proof libraries | Meaning of the submitted statement and imported definitions | Review notation, theorem inventory, dependencies, and changes. Axiom inspection alone does not establish the intended meaning. |
| Formal evaluator compilation and JSON reader | Executed reference results | Executable tests compare values, traps, and input rejection. Finite expression and program evaluator correspondence is proved in both directions; program completeness quantifies sufficient depth and fuel. Typed program results cannot be invalid. Neither termination nor completeness at fixed CLI limits is established. Running compiled Lean still trusts its compilation and runtime, and the JSON adapter is tested rather than proved. |
| Source lexer, parser, resolver, and elaborator | Correspondence between user source and formal core | Implemented and tested for scalar programs and file modules, including scope, visibility, numeric boundaries, retained source locations, and serialized core comparisons. Module resolution and source elaboration remain correspondence obligations. |
| Production type checker | Rejection of ill-typed source programs | Implemented and tested for M1; checked Program contents cannot be constructed or mutated through the safe public Rust API. The abstract typing relation and Lean inference theorems do not prove this checker sound. |
| Ownership and effect checkers | Memory safety, race prevention, and capability restrictions | Unimplemented initially. Formal rules, adversarial tests, and correspondence obligations are required before claims. |
| Verification IR construction and VCG | Whether a discharged formula implies the requested source property | The Rust verifier is implemented and independently tested for pure acyclic functions. A separate Lean call-free generator and contract logic are proved sound under interpreted obligations. Call expansion, callee-precondition insertion, named decomposition, and production correspondence remain unproved (partial FM-07). |
| SMT serializer, solver, and result parser | Solver-backed proof results and counterexamples | Z3 5.3.3 is pinned. The driver records exact tool/query hashes, bounds time and I/O, validates status/models, and requires successful process termination. Real-solver and failure-protocol tests passed in Linux/macOS CI at `a7e0b38591ba76255e561cda60099bc8bc422543` ([run](https://github.com/djsydney04/ANL/actions/runs/44051779446)). Results remain `smt-trusted`; models are unreplayed and no certificate checker is implemented. |
| Compiler transformations | Preservation of values, traps, effects, and divergence properties | Source blocks and modules lower to a typed function table, then validated structured MIR, with tested scope, ordering, branches, and traps. These validators do not prove translation correctness. APL optimization passes remain unimplemented. |
| C or LLVM backend, assembler, and linker | Machine code correctness | The C11 backend is implemented and tested at `-O0`/`-O2`, including checked arithmetic and sanitizer probes. Native and module checks passed macOS AArch64 and Linux x86-64 CI at `19d726c`; compiler, linker, and host behavior remain trusted. LLVM is planned. |
| Runtime and allocator | Cleanup, layout, I/O, concurrency, and memory safety | Scalar arithmetic/trap/output helpers are implemented and tested. Heap allocation, resource cleanup, source I/O, and concurrency runtimes remain unimplemented; they require contracts, sanitizers, and independent unsafe-code review. |
| Unsafe APL and foreign libraries | Any safe abstraction that depends on them | Explicit contracts, versioned dependencies, and reviewed wrappers. Foreign violations can invalidate dependent safety claims. |
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
(FM-06) and lowering proofs (FM-08) remain open. FM-07 has a checked call-free
foundation, but production verification is not kernel checked: call inlining,
callee preconditions, named decomposition, Rust generation, SMT translation, and
solver answers remain trusted or tested boundaries. Module visibility is checked
by Rust before flattening to scalar core; the model's function theorems do not
prove that source-level boundary.

## Proof integrity policy

Foundational proofs must be rebuilt from reviewed source with the pinned proof tool. Incomplete terms, admitted statements, custom proof-bypassing axioms, disabled kernel checking, and native-evaluation trust axioms are excluded from the theorem inventory. Allowed standard logical axioms are listed explicitly in the formal strategy. Dependencies cannot hide a disallowed axiom.

The inventory maps the theorem's actual quantified statement to its advertised claim. Reviewers check that hypotheses are satisfiable and do not assume the conclusion. A theorem about the constructor `True` does not establish a property of APL merely because its name says "compiler_correct". A proof that assumes the entire Rust checker is sound does not prove that checker sound.

Proof status is per semantic revision. Changing grammar elaboration, arithmetic, evaluation order, ownership rules, or lowering invalidates affected correspondence evidence until rechecked. A stale proof file that still builds can describe an obsolete model.

## Verification and external assumptions

The current verifier checks every loaded function and rejects recursive call
graphs. It checks callee preconditions and expands actual bodies, without using
postconditions as summaries. Ordered definedness checks prevent self-justifying
preconditions, and separate satisfiability checks reject vacuous contracts.
Ordinary compilation type-checks and erases clauses without proving or dynamically
checking them. The [verification guide](../verification.md) explains result scope.
Future library summaries and environment assumptions must be explicit; a verified
caller cannot hide an unverified callee behind an empty contract.

External I/O, time, failures, cancellation, and foreign functions enter through modeled events. Verification can establish properties conditional on an event contract. It cannot establish that an external service honors the contract. Agent approvals must be represented by unforgeable authority in the execution model; a string saying "approved" is not authority.

A deterministic replay test confirms behavior for its recorded trace and input state. It does not prove all possible tool responses, schedules, network failures, or model outputs safe. Resource budgets require checked accounting at the actual execution boundary.

## Release claim review

Before a release, enumerate every public safety or verification claim. Link each to a theorem, validator, test, or runtime mechanism and its limits. Verify that unsupported features and targets are visible in CLI diagnostics and documentation. Inspect the actual artifacts and rerun the relevant checks.

The initial release process must include independent checks of integer overflow and division semantics, source-to-core scope handling, solver failure behavior, package integrity, unsafe interfaces, and capability boundaries when those features exist. Missing evidence blocks the corresponding claim or release requirement. It cannot be cured by describing the intended design.
