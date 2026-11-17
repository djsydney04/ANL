# Compiler and ecosystem research

Status: architectural recommendations, not implemented capabilities. Sources were consulted on 2026-11-16.

## The decision being made

APL needs an executable mathematical core, a native compiler, and a usable language ecosystem. The compiler must retain APL's meaning before delegating code generation. Tooling and agents must use the same types, modules, and diagnostics as ordinary programs.

Two complete designs were considered. Design A uses Rust for the compiler, an APL-owned typed core, a separately implemented Lean evaluator, checked C11 for initial native compilation, and an LLVM backend for mature optimization. Design B uses Lean for both elaboration and executable semantics, then extracts or compiles the compiler and lowers directly to a backend. Design B reduces duplicated core definitions but ties diagnostics, incremental compilation, and ecosystem integration to the proof implementation. Design A provides independent implementation evidence and separates compiler concerns from proof infrastructure, at the cost of a conformance problem between the Rust and Lean implementations. Recommend A, with that conformance problem treated as a release requirement.

## Implementation language comparison

| Candidate | Benefit for APL | Cost and trust implications | Recommendation |
| --- | --- | --- | --- |
| Rust | Algebraic data types model syntax and IR; ownership supports a memory-safe compiler implementation; native deployment and package tooling | A Rust compiler does not prove the implemented APL rules; borrowed compiler data structures can complicate incremental analysis | Use owned IDs and immutable pass results. Pin Rust 1.99.1 for the initial implementation. |
| OCaml | Pattern matching and functional transformations fit compiler passes | Managed compiler memory is acceptable, but adds a second deployment ecosystem alongside Lean and native tools; ownership analysis remains custom | Strong alternative, no compelling project-specific advantage over Rust at present. |
| C++ | Direct LLVM and MLIR integration | More manual memory and lifetime hazards in the compiler; larger review burden | Restrict to a backend bridge only if required by measured integration constraints. |
| Lean | Direct proximity to mechanized definitions and proofs | Proof-friendly representations and interactive compiler representations have different needs | Own the formal model and proof checker integration, not the first complete frontend. |
| Self-hosted APL | Exercises the language and can eventually reduce implementation-language fragmentation | Requires bootstrapping and obscures compiler defects before APL is mature | Reconsider after external programs and release qualification. No self-hosting prerequisite. |

Rust's ownership rules are compiler-checked memory-management rules, as described in [the Rust book](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html). This is evidence for an implementation-language choice, not a proof about APL.

## Backend comparison

| Backend | Semantic and engineering properties | Performance implications | Decision |
| --- | --- | --- | --- |
| C11 plus Clang or GCC | Small inspectable emitted programs, native object/linking infrastructure, broad platform availability. Must explicitly avoid C signed overflow and evaluation-order differences. Source mapping is limited. | Can benefit from mature C optimization, but generated layout and alias descriptions may constrain optimizers. No measured APL result yet. | Initial native milestone. Emit explicit temporaries and checked helpers. Retain as a conformance comparison backend while useful. |
| LLVM | Typed SSA, native targets, optimization and debug metadata. APL must handle poison and undefined-behavior rules correctly. Backend version is a build input. | Suitable candidate for vectorization, specialization and native optimization. APL performance remains unmeasured. | Intended production optimization backend after the native baseline. Acceptance requires differential tests and measured results, not feature-count claims. |
| Cranelift | Rust library interface and a defined-behavior IR; AOT and JIT support. Supports x86-64 and AArch64 among other targets. | Prioritizes compiler latency over aggressive optimization. Its published results are not APL measurements. | Strongest alternative to LLVM for development builds. Do not implement another backend without evidence of compile-latency need. |
| MLIR | Multiple abstraction levels and reusable dialect infrastructure, with loop/tensor representations | Attractive for future HPC transformation programs, but introduces substantial dialect and lowering work | Defer until representative workloads require transformations awkward in APL's own IR. No dependency for scalar M1/M2. |
| CompCert | A verified C compilation strategy with explicit supported semantics and a separately documented trust boundary | APL-to-C translation is still outside the proof; target and C subset compatibility require investigation | Research comparator, not a basis for calling APL's compiler verified. |

LLVM's [language reference](https://llvm.org/docs/LangRef.html) defines its IR and instruction contracts. Its [undefined-behavior manual](https://llvm.org/docs/UndefinedBehavior.html) explains why a frontend must preserve conditions before emitting potentially invalid operations. This motivates keeping overflow and trap operations explicit in APL IR.

The [Cranelift project](https://cranelift.dev/) describes its embeddable Rust backend and deliberately defined-behavior IR. The [MLIR rationale](https://mlir.llvm.org/docs/Rationale/Rationale/) explains multi-level lowering and structured loop representations. The [CompCert manual](https://compcert.org/man/manual002.html) bounds the behavior-preservation claim of its compilation chain. These systems inform APL's choices; their guarantees do not transfer to APL's frontend.

## Agent design comparison

Dedicated `agent` syntax could make protocols visible but would create a second execution model before ordinary effects and ownership are stable. A typed library over functions, algebraic data types, capabilities, channels, and structured tasks reuses the same safety analyses. Recommend the library approach. Introduce syntax only after a concrete unexpressible semantic requirement appears.

Ambient global credentials make invocation convenient but defeat local authority reasoning. Opaque capability values provide an explicit authority path. Capabilities must carry a runtime restriction, not merely a phantom type. [Cap'n Proto's RPC model](https://capnproto.org/rpc.html) is a useful example of passing authority-bearing references. APL does not depend on that wire protocol.

Replay can reexecute a deterministic state transition against recorded observations. Replaying arbitrary network calls would repeat side effects and cannot establish durable correctness. [Temporal's replay model](https://docs.temporal.io/workflow-execution) compares generated commands against recorded event history. APL adopts the separation between deterministic decisions and external activities, with explicit handling for an unknown remote result after a crash.

## Toolchain design comparison

One CLI with a compiler library avoids separate command implementations drifting in syntax and diagnostics. An editor invokes that library through LSP rather than parsing human-readable CLI errors. [LSP 3.17](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/) provides the protocol baseline; APL must still implement and test the requested capabilities.

Package manifests express intent and lockfiles capture resolved identities. [Cargo's manifest and lockfile design](https://doc.rust-lang.org/cargo/guide/cargo-toml-vs-cargo-lock.html) provides a practical precedent. APL additionally includes language edition, runtime ABI, compiler version, target, and verification assumptions in artifact keys. Locking inputs is necessary but insufficient for bitwise reproducibility.

Releases need authenticated metadata as well as hashes. [The Update Framework specification](https://theupdateframework.github.io/specification/latest/) provides a design to evaluate for update authenticity, expiry, and rollback resistance. A checksum downloaded beside a binary is not independent authentication. A full TUF service is not an M1 dependency.

## Risks and decision triggers

1. Rust, Lean, C and LLVM disagree on edge cases. Maintain independent, adversarial conformance cases before enabling optimizations.
2. Proof coverage stops at a small expression fragment. Publish the exact grammar covered by each theorem and reject unsupported verification claims.
3. Multiple backends consume engineering effort. The C11 route earns its place by delivering a native baseline; retain further backends only with measured benefit or independent validation value.
4. Durable workflows accidentally promise exactly-once external effects. Model ambiguous outcomes explicitly and require remote idempotency or reconciliation.
5. Toolchain convenience creates hidden ambient authority. Build scripts are disabled by default; package fetches and tool capabilities are explicit.
6. APL is also an established language name. Resolve distribution identifiers and branding before a public package registry launch.

## Implementation dependencies

The [compiler contract](../architecture/compiler.md), [agent architecture](../architecture/agents.md), and [toolchain architecture](../architecture/tooling.md) define the proposed integration boundaries. The first implementation milestone contains the lexer, parser, name resolution, checker, interpreter and independently checked formal core. Native compilation, agent libraries, packages and proofs require their own executable acceptance evidence.
