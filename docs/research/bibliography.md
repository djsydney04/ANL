# Research bibliography

These primary sources inform the language and architecture proposals. Their
results apply to the systems they describe; they do not establish APL's safety,
performance or implementation correctness. The research documents explain how
each source affects a proposed decision.

## Types, memory and effects

| Source | Relevance to APL |
| --- | --- |
| [Dunfield and Krishnaswami, Bidirectional Typing](https://arxiv.org/abs/1908.05839) | Synthesis and checking, explicit boundaries, and inference tradeoffs |
| [Tofte and Talpin, Region-Based Memory Management](https://www.sciencedirect.com/science/article/pii/S0890540196926139) | Region allocation as an alternative to universal ownership and mandatory GC |
| [OCaml manual, Polymorphism and its limitations](https://ocaml.org/manual/5.3/polymorphism.html) | Limits on generalization in the presence of mutable state |
| [Leijen, Koka: Programming with Row Polymorphic Effect Types](https://www.microsoft.com/en-us/research/publication/koka-programming-with-row-polymorphic-effect-types/) | Effect rows, inference and the relationship between effects and evaluation |
| [Rust Reference, Pointer types](https://doc.rust-lang.org/reference/types/pointer.html) | Shared and exclusive references as a design precedent |
| [Rustonomicon, Send and Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) | Separate conditions for transferring ownership and sharing references across threads |
| [RustBelt](https://plv.mpi-sws.org/rustbelt/) | Proof obligations for unsafe implementations behind safe library interfaces |
| [The Rust Programming Language, Understanding ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) | Memory-management properties of the proposed compiler implementation language |

## Formal semantics and verification

| Source | Relevance to APL |
| --- | --- |
| [Lean reference, Validating proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) | Kernel checking, axiom inspection and the distinction between theorem meaning and proof validity |
| [Rocq documentation](https://rocq-prover.org/docs) | Alternative mechanization environment |
| [K tutorial, Proving properties](https://kframework.org/k-distribution/k-tutorial/1_basic/22_proofs/) | Executable operational semantics and deductive verification |
| [Z3 guide, Basic commands](https://microsoft.github.io/z3guide/docs/logic/basiccommands/) | Solver result semantics, including unknown outcomes |
| [Boogie](https://www.microsoft.com/en-us/research/project/boogie-an-intermediate-verification-language/) | Verification IR and VC generation as an alternative to a direct APL encoding |
| [Why3](https://why3.org/) | Proof sessions, logical theories and multiple provers |
| [CompCert manual, Introduction](https://compcert.org/man/manual001.html) | The precise scope and assumptions of a compiler preservation theorem |
| [CompCert manual, The CompCert C compiler](https://compcert.org/man/manual002.html) | Supported compilation behavior and interfaces |
| [Alive2](https://github.com/AliveToolkit/alive2) | LLVM transformation validation as a possible complement to APL-specific proofs |

## Native compilation

| Source | Relevance to APL |
| --- | --- |
| [LLVM language reference](https://llvm.org/docs/LangRef.html) | IR instructions, attributes and backend invariants |
| [LLVM undefined behavior](https://llvm.org/docs/UndefinedBehavior.html) | Poison, undefined behavior and conditions the frontend must preserve |
| [LLVM tutorial, Adding debug information](https://llvm.org/docs/tutorial/MyFirstLanguageFrontend/LangImpl09.html) | Source mappings for native debugging |
| [Cranelift](https://cranelift.dev/) | Alternative backend with a defined-behavior IR and emphasis on compilation latency |
| [MLIR rationale](https://mlir.llvm.org/docs/Rationale/Rationale/) | Multi-level lowering and structured representations for future workloads |

## Capabilities, workflows and tooling

| Source | Relevance to APL |
| --- | --- |
| [Cap'n Proto RPC](https://capnproto.org/rpc.html) | Explicit authority-bearing references |
| [Temporal workflow execution](https://docs.temporal.io/workflow-execution) | Deterministic decisions, event histories and replay |
| [Language Server Protocol 3.17](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/) | Editor/compiler communication |
| [Cargo manifests and lockfiles](https://doc.rust-lang.org/cargo/guide/cargo-toml-vs-cargo-lock.html) | Declared dependency intent versus resolved package identity |
| [The Update Framework specification](https://theupdateframework.github.io/specification/latest/) | Authenticated update metadata, expiration and rollback protection |

## Design comparisons

- [Language and memory research](language-and-memory.md)
- [Formal-methods research](formal-methods.md)
- [Compiler and ecosystem research](compiler-and-ecosystem.md)
- [Architecture decisions](../architecture/decisions.md)
