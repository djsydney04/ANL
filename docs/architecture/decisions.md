# Architecture decisions

These proposed decisions define one compatible implementation direction. Technical
review is pending. They establish no implemented feature, theorem or measured
performance result. Each decision can change when executable evidence supports
a better approach.

## AD-01: explicit types at interfaces, inference within functions

Use explicit function signatures, bidirectional local checking and nominal data
types. Add explicit rank-1 generics after the scalar core. Hindley-Milner inference
with generalization at arbitrary local bindings is the strongest alternative.
Explicit interfaces simplify separate checking and reduce ambiguity around mutable
state and ownership, at the cost of annotations. The design follows the distinctions
in [bidirectional typing](https://arxiv.org/abs/1908.05839) and the
[OCaml polymorphism discussion](https://ocaml.org/manual/5.3/polymorphism.html).
The algorithmic checker must agree with the declarative judgments; inference
convenience cannot weaken them.

## AD-02: affine resources with shared and exclusive borrows

Use one destruction responsibility per owned resource and lexical loans initially.
Region inference, reference counting, and tracing GC remain alternatives or optional
library mechanisms. Explicit ownership fits FFI and non-memory resources, while
lexical loans reduce initial analysis complexity. The cost is conservative
rejection of some valid programs. [Region-based memory management](https://www.sciencedirect.com/science/article/pii/S0890540196926139)
informs the arena alternative; [RustBelt](https://plv.mpi-sws.org/rustbelt/)
motivates obligations for unsafe wrappers. Heap safety requires its own store,
permission, lifetime and cleanup proofs beyond scalar typing.

## AD-03: checked scalar semantics before heap extensions

The first core contains `i64`, `bool`, unit, immutable bindings, conditionals and
typed named calls. Arithmetic traps are defined in every build mode. Operands
evaluate left to right, with explicit short-circuit behavior. Wrapping arithmetic
and backend-dependent overflow would simplify some lowering but conflict with
predictable source meaning. The compiler, interpreter and formal model must agree
on values, traps and evaluation order. Tool resource limits remain distinct from
language behavior. The [type-system specification](type-system.md) is normative.

## AD-04: Rust compiler and independent Lean semantics

Use Rust 1.99.1 for the initial compiler and Lean 4 for mechanized definitions and
metatheory. OCaml is a strong compiler alternative; a Lean frontend could reduce
duplicated definitions. Separate implementations support independent comparisons
and keep compiler usability concerns outside proof representations. The cost is
an explicit correspondence obligation. [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
requires attention to both theorem statements and axiom dependencies. A proof
about the Lean model does not certify the Rust parser, checker or evaluator.

## AD-05: direct verification conditions with explicit solver trust

Start with an ANL verification IR and weakest-precondition generation for a bounded
pure fragment, emitting SMT-LIB to Z3. [Boogie](https://www.microsoft.com/en-us/research/project/boogie-an-intermediate-verification-language/)
and [Why3](https://why3.org/) are concrete alternatives before extending the encoding
to mutable heaps. Direct encoding retains source locations and checked arithmetic,
but ANL must establish substitution, path-condition and encoding soundness. Preserve
solver `unknown` outcomes and distinguish trusted-SMT results from kernel-checked
artifacts. Termination, trap freedom and postconditions are separate obligations.

## AD-06: C11 native baseline followed by evaluated LLVM lowering

Use explicit temporaries and checked helpers in the first C11 backend. LLVM is the
intended optimizing backend; Cranelift is an alternative if compilation latency
justifies it. MLIR requires representative workloads before adding another IR
framework. [LLVM's undefined-behavior rules](https://llvm.org/docs/UndefinedBehavior.html)
make backend invariants part of the correctness problem. C11 offers an inspectable
native baseline but introduces ordering, overflow and deployment obligations.
Acceptance requires native execution and independent semantic comparison, including
traps. Neither backend choice establishes a performance advantage or compiler proof.

## AD-07: runtime components follow language capabilities

Scalar programs need entry, trap and linking support. Allocation, I/O, threads,
async and observability add runtime components when used. Start concurrency with
scoped ownership transfer and sequentially consistent atomics. A universal managed
runtime is simpler for unrestricted sharing but adds mandatory overhead and weakens
control of reclamation. The [runtime specification](runtime.md) requires explicit
cleanup, cancellation, ABI and synchronization semantics. Race freedom does not
imply deadlock freedom or successful cancellation of remote operations.

## AD-08: agents as typed libraries with enforced capabilities

Build agent applications from ordinary types, tasks, messages and opaque
capabilities. Dedicated syntax would introduce a second execution model before
the general language is mature. [Capability-oriented RPC](https://capnproto.org/rpc.html)
and [workflow replay](https://docs.temporal.io/workflow-execution) inform the library
boundaries. Authority must be checked at runtime, and replay must use recorded
observations rather than repeat external effects. Protocol proofs cover named
transitions and assumptions; they cannot establish the truth of external responses.

## AD-09: one semantic toolchain with locked package identities

The CLI and language server share compiler APIs. Package manifests declare intent,
and lockfiles capture resolved identities as in [Cargo](https://doc.rust-lang.org/cargo/guide/cargo-toml-vs-cargo-lock.html).
Independent command implementations are easier to isolate but risk inconsistent
typing and diagnostics. Shared APIs require stable structured diagnostics and
versioned interfaces. Build and proof cache keys include all relevant semantic
inputs. Native build scripts are disabled by default. Clean installation and
reproducibility checks must validate the actual distributed artifacts.

The [overview](overview.md) connects these choices. The [research bibliography](../research/bibliography.md)
lists their sources, and the [requirements](../requirements.md) define acceptance.
