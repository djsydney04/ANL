# Language and memory research

Status: design recommendation, pending technical review. This document does not establish implementation or proof coverage.

The proposed design is a strict, expression-oriented language with explicit function signatures, local bidirectional inference, affine ownership, and shared or exclusive borrowing. The first executable milestone contained only scalar values. The current implementation also includes local state, flat tuples and [scoped `i64` buffers](../../spec/owned-buffers.md) with read/edit call views. Its [separate memory model](../../formal/PROOFS.md#owned-buffers-and-coremir-correspondence) establishes finite scoped safety and canonical Core/MIR correspondence; the broader design alternatives below remain research direction.

## Two complete candidate designs

| Question | Candidate A: inferred functional language with regions | Candidate B: explicit interfaces with affine ownership |
| --- | --- | --- |
| Types | Hindley-Milner inference, let polymorphism, nominal data types | Declared function signatures, bidirectional local inference, explicit rank-1 generics |
| Memory | Compiler-inferred region allocation, with optional reference counting for escaping values | One owner per resource, explicit shared or exclusive borrows, deterministic cleanup |
| Effects | Inferred type-and-effect rows | Explicit exported effect bounds, inferred internal effect sets; row polymorphism added for higher-order APIs |
| Functional code | Broad inference and convenient closures | Annotated boundaries; closure captures carry ownership and call restrictions |
| Systems code | Region lifetime and retained-space behavior can be hard to predict | Ownership moves and allocation sites are explicit; borrowing can reject useful programs |
| Verification | Region soundness and effect-inference correspondence | Ownership soundness, borrow-checker correspondence, destructor and concurrency invariants |
| Runtime | Region stacks, escape strategy, optional reference counts | Stack frames and allocator; additional runtime components linked only when used |

Candidate A is credible. Tofte and Talpin describe a region discipline for higher-order programs without a mandatory garbage collector, including a soundness argument. Regions remain useful for ANL arenas and request-scoped allocation. Selecting them as the universal memory discipline would make allocation lifetime inference part of every systems-programming explanation. [Tofte and Talpin, 1997](https://www.sciencedirect.com/science/article/pii/S0890540196926139)

Candidate B is the recommendation because ANL requires native interoperability, explicit resource lifetimes, and predictable cleanup of non-memory resources. It also gives the verifier a local permission model. This is an engineering judgment, not a demonstrated performance advantage. ANL must prove its own rules; borrowing syntax similar to Rust provides no evidence of soundness.

## Type-system choices

The following judgments are design assessments for ANL. They are not measured compiler costs.

| Feature | Decision and role | Soundness and verification consequence | Complexity, diagnostics, and performance consequence |
| --- | --- | --- | --- |
| Hindley-Milner inference | Use unification within expressions; do not infer public signatures or generalize arbitrary local lets | Avoid unconstrained generalization of mutable storage | More annotations at boundaries; predictable local errors and separate compilation |
| Bidirectional checking | Adopt synthesis for eliminations and checking against declared types | Prove algorithmic checking agrees with declarative rules | Controls ambiguity for closures and generics; linear-looking traversals still need measured unification costs |
| Parametric polymorphism | Explicit rank-1 generic functions and nominal data types | Generic bodies checked once under abstract parameters; specialization must preserve typing | Native monomorphization avoids mandatory dictionary dispatch, with compile-time and code-size risks |
| Type classes or traits | Adopt coherent nominal traits with explicit bounds after generics | Reject overlapping implementations; no unchecked structural casts | Gives collections and operators shared APIs; defer specialization and higher-order instance search |
| Linear types | Reserve for protocols requiring consumption, after affine core | Exact use can express completion obligations but exceptions/cancellation complicate proofs | Too restrictive as universal rule; explicit protocol APIs before general linear syntax |
| Affine types | Adopt owned values used at most once, with compiler-inserted cleanup | Must prove moves invalidate previous ownership and cleanup does not duplicate resources | No required reference-count traffic; move diagnostics need source paths |
| Regions and lifetimes | Adopt lexical loan regions first; explicit lifetime parameters at exported reference boundaries later | References cannot outlive storage; reborrow suspends parent access | Conservative rejection is acceptable initially; non-lexical inference requires equivalence evidence |
| Refinements | Add specification predicates checked by a verifier, not ordinary type inference | Successful proof has a stated fragment and solver assumptions; unknown does not become success | Verification cost is explicit and bounded independently of compilation |
| Dependent types | Restrict initial use to compile-time natural array lengths and ghost specifications | No arbitrary program evaluation in definitional type equality | Keeps ordinary checking decidable and diagnostics practical; full dependent types remain a research option |
| Effect systems | Adopt finite effects at boundaries, then effect variables for higher-order composition | Effects constrain possible behavior; they do not supply authority or prove termination | Internal inference reduces annotations; open-row inference and handlers need a later formal extension |
| Capability types | Adopt opaque resource values passed explicitly to APIs | Constructor privacy plus ownership prevents safe-code fabrication; host must provision authority | Small handles can erase or lower directly; raw FFI remains trusted |
| Typestate | Encode states as generic parameters on opaque owned handles | Transitions consume the old state; external revocation still needs runtime checks | No special syntax needed; avoids runtime tags where state is statically known |
| Session types | Begin with typestate channel libraries; evaluate multiparty systems after concurrency | Protocol conformance differs from deadlock freedom, fairness, and delivery | Cancellation and peer failure require explicit terminal states; reject global liveness claims |
| Higher-kinded types | Defer until a concrete library cannot express its API with traits and associated types | Avoid adding higher-order unification to the initial checker | Lower implementation burden; reconsider using real library evidence |

Bidirectional typing separates synthesis from checking and can improve error locality while supporting types that do not admit unrestricted inference. That supports ANL's explicit-boundary choice. [Dunfield and Krishnaswami, 2021](https://arxiv.org/abs/1908.05839)

OCaml's treatment of weak polymorphism illustrates why a mutable cell cannot be generalized like an immutable mathematical value. ANL initially keeps local bindings monomorphic and quantifies only declared generic parameters. [OCaml manual, polymorphism and its limitations](https://ocaml.org/manual/5.3/polymorphism.html)

Koka demonstrates a principled relationship between effect types and evaluation properties. ANL adopts the requirement to define that relationship, but does not inherit Koka's theorems or assume its inference algorithm applies unchanged to affine ownership. The source explicitly records a corrected lemma, reinforcing the need to pin and independently check actual proof artifacts. [Leijen, Koka](https://www.microsoft.com/en-us/research/publication/koka-programming-with-row-polymorphic-effect-types/)

## Memory alternatives

| Approach | Strength | Cost or limitation | ANL decision |
| --- | --- | --- | --- |
| Mandatory tracing GC | Supports cyclic graphs and unrestricted shared references | Collector runtime, tracing interfaces at FFI, and less direct control of reclamation | Exclude as a universal requirement; explicit managed arena may be added later |
| Automatic reference counting | Local reclamation and convenient sharing | Counter updates, cycles, atomic overhead across threads | Optional `Rc` and `Arc` library ownership types with documented cycle behavior |
| Pure linear ownership | Strong exactly-once accounting | Ordinary ignored values, failure, and cancellation require explicit discharge | Use only where protocol obligations justify it |
| Affine ownership and borrowing | Predictable storage ownership and zero-runtime lexical loans | Borrow checker and aliasing semantics are substantial proof obligations | Selected default |
| Region allocation | Cheap bulk reclamation and natural phase lifetimes | Over-retention within long regions; escaping values need disciplined handling | Library arenas with typed lifetime bounds |
| Mutable value semantics | Local reasoning and fewer first-class aliases | Copy or uniqueness analysis costs; restrictive recursive graph APIs | Useful comparison, but less direct fit for explicit FFI and borrowed slices |

Rust's shared and mutable reference distinction is a useful operational precedent. ANL initially excludes interior mutability from ordinary shared references. Any later synchronization or cell abstraction must supply a separate invariant. [Rust Reference, pointer types](https://doc.rust-lang.org/reference/types/pointer.html)

RustBelt supplies an important architectural lesson: proving a safe language core is insufficient if unsafe libraries violate the semantic meaning of its types. ANL therefore treats allocator, synchronization, and FFI wrappers as explicit verification and review targets. [RustBelt project](https://plv.mpi-sws.org/rustbelt/)

## Effects, authority, and concurrency

An effect says an operation may happen. A capability says a particular operation is authorized. An `io` effect must not fabricate a filesystem handle, and an `unsafe` block must not fabricate host permissions. Capability-bearing handles are opaque and non-`Copy` unless their provider deliberately permits duplication.

Cross-thread ownership transfer and shared-reference use require separate `Send` and `Sync` properties. Rust demonstrates why an unsynchronized reference counter or interior-mutable cell cannot receive those properties automatically. ANL will define its own structural derivation rules and audit every trusted exception. [Rustonomicon, Send and Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html)

The initial concurrency model uses scoped tasks, owned messages, locks, and sequentially consistent atomics. Relaxed atomics remain a separately reviewed extension. This reduces the first model's complexity without turning data-race freedom into a claim about deadlock freedom or distributed reliability.

## Integration decisions and open risks

The scalar M1 contract includes `i64`, `bool`, `unit`, explicit function signatures, immutable lets, conditionals, named calls, checked arithmetic, and left-to-right evaluation. The [type-system specification](../architecture/type-system.md) and [grammar](../../spec/grammar.ebnf) define that contract. The native compiler must preserve the same defined traps.

The scoped-buffer model now covers initialized fixed-length storage and recursive call-scoped views. General affine owner moves, aggregate and escaping borrows, and concurrent library abstractions still require additional semantics and proofs; neither M1's scalar theorem nor the scoped subset discharges them. Other risks are specialization explosion, useful diagnostics for lifetime constraints, effect-polymorphic closure soundness, FFI aliasing, and cancellation during external operations.

Reference support requires a reviewed store-and-permission model, a proof of its core preservation property, and rejection tests for use-after-move, escaping borrows, mutable aliasing, and partial initialization. Shared-memory concurrency requires defined synchronization semantics and adversarial tests for capability transfer and cancellation.

## Scope of the comparison

This comparison covers whole-language foundations and the advanced type features in the language requirements. It identifies implementation dependencies and future proof obligations. The cited sources support design choices; they supply no evidence of ANL implementation performance or machine-checked safety.
