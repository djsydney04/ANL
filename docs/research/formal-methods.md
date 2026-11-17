# Formal methods research

Status: design recommendation, subject to technical review. No APL theorem or verifier is implemented by this document.

## Decision

Use Lean 4 for APL's mechanized semantics and metatheory. Build the practical verifier around an APL-owned verification IR and verification-condition generator, initially emitting SMT-LIB to Z3. Keep solver-backed program verification and kernel-checked language theorems as distinct evidence classes. Add proof certificates only when their checker and connection to APL semantics exist.

This choice gives the language a small executable formal core without making every programmer write proof terms. It also leaves the compiler implementation independent of a proof assistant's extraction backend. That independence creates a correspondence obligation which must remain visible.

## Mechanization alternatives

| Candidate | Evidence and advantages | Costs for APL | Decision |
| --- | --- | --- | --- |
| Lean 4 | Dependent types, inductive relations, executable definitions, and kernel checking fit a typed expression core and reusable transformation lemmas. Its reference describes proof validation and axiom inspection. | APL still needs its own language semantics, binder infrastructure, heap model, and compiler correspondence. Executing compiled Lean is not the same evidence as checking a proof. | Select for one maintained formal model. Begin without third-party theorem libraries unless a concrete obligation needs them. |
| Rocq | A strong alternative for operational semantics, extraction, and verified compilation. CompCert provides a working example of compiler proofs in this ecosystem. | Selecting Rocq would be defensible, but maintaining parallel Lean and Rocq models would divide effort and multiply synchronization obligations. | Retain as the strongest alternative. Revisit if reuse of a specific compiler or separation-logic development outweighs migration cost. |
| K | Executable operational rules, symbolic execution, and deductive program verification can share one semantics. This is attractive for reference execution and semantic experiments. | APL would need to evaluate its typed binding representation, proof artifact checking, installation costs, and compiler integration. K's generated execution tools do not by themselves prove the independent APL compiler correct. | Do not maintain a second normative model initially. Use only for a bounded experiment if Lean semantics becomes an evidenced bottleneck. |

The selection is an engineering judgment, not a claim that Lean is more expressive, faster, or more trustworthy than Rocq. No comparative performance experiment has been run. Lean's documentation explicitly separates theorem meaning, axiom auditing, and replay through a checker. Rocq's documentation links both foundational materials and its reference. K documents executable semantics and deductive verification. [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/), [Rocq documentation](https://rocq-prover.org/docs), [K verification tutorial](https://kframework.org/k-distribution/k-tutorial/1_basic/22_proofs/).

## Program verification alternatives

| Approach | Benefit | Limitation | APL choice |
| --- | --- | --- | --- |
| Direct APL VCG and SMT-LIB | Exact control of checked arithmetic, source spans, obligation names, and trust reporting. A small pure fragment can have a corresponding Lean soundness theorem. | APL owns substitution, path conditions, framing, and encoding correctness. | Initial route, limited to an explicitly supported fragment. |
| Boogie verification IR | Existing VC generation and SMT integration. Reduces infrastructure work for imperative verification. | Adds a semantic translation and tool dependency; APL must model ownership, traps, and effects accurately. | Benchmark as a competing route before extending the direct VCG to heaps and complex loops. |
| Why3 and WhyML | Multiple prover support, proof sessions, logical theories, and uses as an intermediate language for other languages. | Adds translation and deployment obligations. Counterexample mapping and APL aliasing still need design. | Strong competing route for data structures and interactive proof sessions. |
| Dependent types throughout APL | Makes specifications expressible in types and supports explicit proof terms. | Changes inference, compilation, erasure, usability, and termination requirements across the language. | Use dependent types in the metatheory; defer them in general source types. |
| Refinement contracts | Ordinary code can acquire predicates without requiring proof terms everywhere. | Decidable inference cannot cover arbitrary predicates; annotations and unknown results remain necessary. | Add contracts over existing types, then constrained refinement inference with explicit limits. |
| Bounded symbolic execution alone | Useful counterexamples and finite-state checks with measurable bounds. | Passing a bound does not establish unbounded safety or termination. | Testing and bounded analysis evidence only; never substitute for an unrestricted proof. |

Boogie describes a language-independent verification layer with VC generation and SMT solving. Why3 offers WhyML, logical theories, and automated or interactive provers. These are practical alternatives, not evidence about APL's correctness. [Boogie project](https://www.microsoft.com/en-us/research/project/boogie-an-intermediate-verification-language/), [Why3 overview](https://why3.org/).

Z3's documented outcomes are `sat`, `unsat`, and `unknown`. The APL driver must preserve that distinction and separate malformed queries, process failures, and timeouts. [Z3 basic commands](https://microsoft.github.io/z3guide/docs/logic/basiccommands/).

## Compiler correctness alternatives

1. Prove each transformation once against explicit IR semantics. This offers broad reusable guarantees but requires stable representations and substantial proofs. Start with a small local simplifier and scalar lowering after the core model is established.
2. Validate each compilation by a separately checked semantic relation. This reduces trust in the optimizing producer but moves trust to the validator and its model. Reject or report unknown when the supported fragment is exceeded.
3. Compare reference and native executions on generated programs. This is immediately useful but remains testing, even with millions of cases.
4. Adopt a verified backend. This helps only when the APL-to-backend translation and its assumptions are justified. Compiling through CompCert would not prove the APL frontend correct, and its supported subset, target support, and license would require separate assessment.

APL adopts the first three in stages. Initial native backends remain trusted, unverified components. CompCert's published theorem begins with an elaborated C AST and ends with an assembly AST; its explicit boundary is a useful model for describing APL's eventual theorem coverage. [CompCert semantic preservation](https://compcert.org/man/manual001.html).

Alive2 demonstrates LLVM optimization validation. It may support future LLVM-specific checks, but validating LLVM transformations cannot establish correctness of APL elaboration or runtime behavior. Pin supported LLVM and validator versions before using it in CI. [Alive2 repository](https://github.com/AliveToolkit/alive2).

## Semantic constraints

The initial core contains `i64`, `bool`, and `unit`; immutable local bindings; typed named functions; recursion; conditional expressions; and strict left-to-right evaluation except short-circuit Boolean operators and unselected branches. Arithmetic is checked. Division truncates toward zero. Both division and remainder trap on zero divisors and `MIN / -1` or `MIN % -1` respectively.

The formal model represents `i64` as mathematical integers restricted to `[-2^63, 2^63-1]`. This avoids accidentally importing host overflow behavior. An internal interpreter fuel limit is an observation limit, not a language trap or proof that a program diverges. Purity excludes external observations; it does not imply totality or trap freedom.

The first mechanized theorem covers the exact scalar expression subset listed in the formal strategy. Functions and recursion receive mathematical semantics immediately; their machine-checked coverage is tracked separately until corresponding theorems pass. Heap, borrowing, concurrency, and FFI proofs require later model extensions. None inherit safety from the scalar theorem automatically.

## Feasibility and dependencies

Before formal implementation, choose an exact stable Lean release with a matching available platform artifact, pin it in `formal/lean-toolchain`, and record installation provenance. Prove a small induction lemma and run an executable definition to check the environment. Add a pinned Z3 distribution when verifier engineering starts. A missing solver must report unavailable verification, never success. Ordinary end users must not need Lean to run compiled programs.

## Risks and decision triggers

| Risk | Required evidence or mitigation |
| --- | --- |
| A correct theorem describes a different language | Independent review compares each constructor, arithmetic corner case, and evaluation order to the compiler contract. Run shared conformance vectors through independent evaluators. |
| A false or vacuous specification is accepted | Audit theorem statements and assumptions. Diagnose unreachable preconditions. Keep invalid-contract and inconsistent-assumption fixtures. |
| SMT translation omits a safety check | Make each possible trap generate an obligation. Mutation tests remove guards and must fail. Prove VCG soundness for the initial pure fragment. |
| Ownership model exceeds current proof expertise | Deliver a smaller explicit borrowing discipline first; extend after formal rules, implementation, and negative tests agree. |
| Heap verification grows into a second compiler | Compare direct VCG against Boogie and Why3 on the same mutable data-structure examples before committing to a larger encoding. |
| Proof checking is hidden behind editor success | Clean pinned builds, explicit theorem inventory, axiom audit, independent review, and checker replay where supported. |
| Testing is reported as translation validation | Record evidence method and coverage per transformation. Require a sound validator or theorem before changing the claim. |

## Research questions that remain open

The exact separation logic for heap contracts, lifetime-parametric proof rules, concurrent interference model, and certificate format for SMT results remain open. These do not block the pure scalar milestone. They do block verified heap and concurrency claims. Agent protocol proofs will reuse state-transition and capability models after the relevant runtime semantics exist.

The project must evaluate whether each broader feature preserves the direct VCG's tractability. There is no commitment to arbitrary quantified refinement inference, full dependent source types, or proof of the entire optimizing backend in the initial release.
