# Trust boundaries and guarantee ledger

Status: M1 evidence ledger for semantic revision `m1-2026-11-16`, with the wider
language still planned. Rust source checking, interpretation, and strict core
import/export have executable conformance coverage. Lean's scalar expression
model has kernel-checked theorems. There is no Rust compiler correctness proof,
function-call safety theorem, program verifier, native backend, or qualified
release. Architecture review alone cannot change a component to verified.

Current evidence is available in the [source conformance tests](../../tests/conformance.rs),
[API and I/O boundary tests](../../tests/boundaries.rs),
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
| Lean kernel and allowed logical axioms | Kernel-checked theorem validity | Lean 4.36.0 is pinned; the expression inventory is checked by clean builds, transitive axiom audit, and kernel replay. Actual dependencies are recorded in the inventory. Hardware and host integrity remain assumptions. |
| Lean elaboration and proof libraries | Meaning of the submitted statement and imported definitions | Review notation, theorem inventory, dependencies, and changes. Axiom inspection alone does not establish the intended meaning. |
| Formal evaluator compilation and JSON reader | Executed reference results | Executable tests compare values, traps, and input rejection. Expression evaluator correspondence is proved in the model; program evaluator correspondence remains FM-05 work. Running compiled Lean still trusts its compilation and runtime, and the JSON adapter is tested rather than proved. |
| Source lexer, parser, resolver, and elaborator | Correspondence between user source and formal core | Implemented and tested for M1, including scope, numeric boundaries, and serialized core comparisons. Source elaboration remains a correspondence obligation. |
| Production type checker | Rejection of ill-typed source programs | Implemented and tested for M1; checked Program contents cannot be constructed or mutated through the safe public Rust API. The abstract typing relation and Lean inference theorems do not prove this checker sound. |
| Ownership and effect checkers | Memory safety, race prevention, and capability restrictions | Unimplemented initially. Formal rules, adversarial tests, and correspondence obligations are required before claims. |
| Verification IR construction and VCG | Whether a discharged formula implies the requested source property | Initially unimplemented; trusted once built until a relevant correctness theorem exists. Each unsupported feature must be rejected. |
| SMT serializer, solver, and result parser | Solver-backed proof results and counterexamples | Pin versions, retain queries, check process status, distinguish unknown and errors. A solver result is trusted until an adequate certificate is independently checked. |
| Compiler transformations | Preservation of values, traps, effects, and divergence properties | Source blocks lower to typed core expressions with tested scope and evaluation order. Optimization and native lowering remain unimplemented; future passes need scoped proofs or translation validators. |
| C or LLVM backend, assembler, and linker | Machine code correctness | Native APL compilation is unimplemented. Record exact versions and targets when introduced. C emission must avoid host undefined behavior; LLVM emission must respect poison and undefined-behavior rules. |
| Runtime and allocator | Cleanup, layout, I/O, concurrency, and memory safety | Unimplemented initially. Use module contracts, sanitizers, runtime tests, and independent unsafe-code review. |
| Unsafe APL and foreign libraries | Any safe abstraction that depends on them | Explicit contracts, versioned dependencies, and reviewed wrappers. Foreign violations can invalidate dependent safety claims. |
| OS and hardware | Execution, scheduling, memory, I/O, and clock assumptions | Explicit platform support and integration tests. A language proof does not verify these components. |
| Package resolution and distribution | Which code and proofs are actually consumed | Locked content hashes, reproducible inputs, provenance, artifact integrity, and clean installation tests. |
| External tools and model providers | Agent observations and effects | Treat responses as untrusted inputs constrained by contracts. No semantic truth guarantee for model-generated content. |

The baseline scope follows the distinction in Lean's proof-validation guidance and CompCert's published compiler theorem boundary. [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/), [CompCert theorem scope](https://compcert.org/man/manual001.html).

## Acceptable evidence labels

`designed` means an accepted specification exists. `implemented` means reachable code exists. `tested` means named tests passed for identified inputs. `type-checked` means the checker accepted a program under a stated language version. `dynamically-checked` describes runtime enforcement on actual executions. `solver-verified` means the supported obligation was discharged under the recorded solver and encoding assumptions. `kernel-checked` identifies an actual theorem and its audited dependencies. `translation-validated` identifies a particular compilation and a validator whose soundness scope is recorded.

Do not collapse these labels into a generic green check. Only the named Lean
expression theorems currently carry the kernel-checked label. Recursive-call
safety (FM-05), Rust/model correspondence proofs (FM-06), VCG soundness (FM-07),
and lowering proofs (FM-08) remain open.

## Proof integrity policy

Foundational proofs must be rebuilt from reviewed source with the pinned proof tool. Incomplete terms, admitted statements, custom proof-bypassing axioms, disabled kernel checking, and native-evaluation trust axioms are excluded from the theorem inventory. Allowed standard logical axioms are listed explicitly in the formal strategy. Dependencies cannot hide a disallowed axiom.

The inventory maps the theorem's actual quantified statement to its advertised claim. Reviewers check that hypotheses are satisfiable and do not assume the conclusion. A theorem about the constructor `True` does not establish a property of APL merely because its name says "compiler_correct". A proof that assumes the entire Rust checker is sound does not prove that checker sound.

Proof status is per semantic revision. Changing grammar elaboration, arithmetic, evaluation order, ownership rules, or lowering invalidates affected correspondence evidence until rechecked. A stale proof file that still builds can describe an obsolete model.

## Verification and external assumptions

Contracts explicitly identify caller preconditions, library summaries, environment assumptions, and safety properties checked. Unproved summaries are assumptions. A verified caller cannot hide an unverified callee behind an empty contract. Preconditions need separate reachability diagnostics to expose vacuous proofs.

External I/O, time, failures, cancellation, and foreign functions enter through modeled events. Verification can establish properties conditional on an event contract. It cannot establish that an external service honors the contract. Agent approvals must be represented by unforgeable authority in the execution model; a string saying "approved" is not authority.

A deterministic replay test confirms behavior for its recorded trace and input state. It does not prove all possible tool responses, schedules, network failures, or model outputs safe. Resource budgets require checked accounting at the actual execution boundary.

## Release claim review

Before a release, enumerate every public safety or verification claim. Link each to a theorem, validator, test, or runtime mechanism and its limits. Verify that unsupported features and targets are visible in CLI diagnostics and documentation. Inspect the actual artifacts and rerun the relevant checks.

The initial release process must include independent checks of integer overflow and division semantics, source-to-core scope handling, solver failure behavior, package integrity, unsafe interfaces, and capability boundaries when those features exist. Missing evidence blocks the corresponding claim or release requirement. It cannot be cured by describing the intended design.
