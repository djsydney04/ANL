# Trust boundaries and guarantee ledger

Status: initial trust ledger. No APL implementation, theorem, verifier, or release has been validated by this document. Later changes must replace these initial entries with exact evidence references; architecture review alone cannot change a component to verified.

## What a claim covers

Every claim records the program or formal artifact, property, semantic revision, supported feature subset, platform, toolchain, assumptions, and evidence method. Type checking, testing, runtime checking, solver discharge, kernel proof, and translation validation remain distinct. A guarantee about one layer does not automatically extend to another layer.

For example, a Lean theorem establishing scalar preservation applies to the formal transition relation and the stated typing judgment. It does not prove the Rust parser implements that judgment, the C emitter preserves traps, or an OS executes a binary correctly. Each connection needs its own evidence.

## Initial trusted components

| Component | What depends on it | Initial evidence and required strengthening |
| --- | --- | --- |
| Language definitions and theorem statements | Whether checked mathematics describes intended APL behavior | Independent technical review, semantic examples, and implementation correspondence tests. Formalizing the wrong statement remains possible. |
| Lean kernel and allowed logical axioms | Kernel-checked theorem validity | Pin version and provenance, audit imported axioms, use clean proof builds and checker replay. Hardware and host integrity remain assumptions. |
| Lean elaboration and proof libraries | Meaning of the submitted statement and imported definitions | Review notation, theorem inventory, dependencies, and changes. Axiom inspection alone does not establish the intended meaning. |
| Formal evaluator compilation and JSON reader | Executed reference results | Test against definitions and fixtures. Running an executable built from Lean trusts that compilation and runtime; checking its theorem is different evidence. |
| Source lexer, parser, resolver, and elaborator | Correspondence between user source and formal core | Initially trusted and tested. Preserve spans, reject ambiguity, test scope and numeric boundaries, and compare serialized core. |
| Production type checker | Rejection of ill-typed source programs | Initially trusted and tested. The abstract typing relation being sound does not prove this checker sound. |
| Ownership and effect checkers | Memory safety, race prevention, and capability restrictions | Unimplemented initially. Formal rules, adversarial tests, and correspondence obligations are required before claims. |
| Verification IR construction and VCG | Whether a discharged formula implies the requested source property | Initially unimplemented; trusted once built until a relevant correctness theorem exists. Each unsupported feature must be rejected. |
| SMT serializer, solver, and result parser | Solver-backed proof results and counterexamples | Pin versions, retain queries, check process status, distinguish unknown and errors. A solver result is trusted until an adequate certificate is independently checked. |
| Compiler transformations | Preservation of values, traps, effects, and divergence properties | Initially unimplemented; use explicit IR invariants and differential tests, then scoped proofs or translation validators. |
| C or LLVM backend, assembler, and linker | Machine code correctness | Unverified trusted components initially. Record exact versions and targets. C emission must avoid host undefined behavior; LLVM emission must respect poison and undefined-behavior rules. |
| Runtime and allocator | Cleanup, layout, I/O, concurrency, and memory safety | Unimplemented initially. Use module contracts, sanitizers, runtime tests, and independent unsafe-code review. |
| Unsafe APL and foreign libraries | Any safe abstraction that depends on them | Explicit contracts, versioned dependencies, and reviewed wrappers. Foreign violations can invalidate dependent safety claims. |
| OS and hardware | Execution, scheduling, memory, I/O, and clock assumptions | Explicit platform support and integration tests. A language proof does not verify these components. |
| Package resolution and distribution | Which code and proofs are actually consumed | Locked content hashes, reproducible inputs, provenance, artifact integrity, and clean installation tests. |
| External tools and model providers | Agent observations and effects | Treat responses as untrusted inputs constrained by contracts. No semantic truth guarantee for model-generated content. |

The baseline scope follows the distinction in Lean's proof-validation guidance and CompCert's published compiler theorem boundary. [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/), [CompCert theorem scope](https://compcert.org/man/manual001.html).

## Acceptable evidence labels

`designed` means an accepted specification exists. `implemented` means reachable code exists. `tested` means named tests passed for identified inputs. `type-checked` means the checker accepted a program under a stated language version. `dynamically-checked` describes runtime enforcement on actual executions. `solver-verified` means the supported obligation was discharged under the recorded solver and encoding assumptions. `kernel-checked` identifies an actual theorem and its audited dependencies. `translation-validated` identifies a particular compilation and a validator whose soundness scope is recorded.

Do not collapse these labels into a generic green check. No claim in this initial document has reached the latter categories merely by being written down.

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
