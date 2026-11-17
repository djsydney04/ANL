# Type-system and executable-core specification

Status: scalar types, flat tuples, functions, modules, typed contracts, initialized mutable
locals, while loops, scoped `i64` buffers and read/edit call views are implemented.
The broader types, movable ownership and
effects below remain design proposals. The [grammar](../../spec/grammar.ebnf),
[local-state rules](../../spec/control-flow.md), and [proof inventory](../../formal/PROOFS.md)
separate source behavior from model guarantees and implementation correspondence.

## Language model

ANL is a strict, statically typed, expression-oriented systems language. Function signatures define module boundaries. Local expressions synthesize types or check against an expected type. There are no implicit numeric conversions, truthiness conversions, dynamically typed escape values, or unchecked downcasts in safe code.

The complete language requires primitive integers and floating-point numbers, Unicode scalar characters, UTF-8 text, arrays, slices, tuples, records, nominal algebraic data types, exhaustive matches, generics, closures, modules, explicit errors, mutation, and ownership. These remain delivery requirements even when a milestone supports a smaller subset.

## Executable types and forms

The current runtime supports these forms:

| Form | Contract |
| --- | --- |
| `i64` | Mathematical integers in `[-2^63, 2^63-1]` with checked operations |
| `bool` | Exactly `true` or `false` |
| `unit` | One value, written `()` |
| `(T1, ..., Tn)` | Flat tuple of 1–8 scalar fields; singleton spelling `(T,)` |
| `tuple.N` | Constant in-bounds field projection; evaluates the complete base |
| `fn name(x: T, ...) -> U { ... }` | Declared parameter and result types, named calls, recursion |
| `let x = e;` or `let x: T = e;` | Immutable, monomorphic local binding |
| `let mut x = e;` or `let mut x: T = e;` | Initialized mutable local with a fixed type |
| `x = e;` | Assign the nearest mutable local after evaluating an identically typed right-hand side |
| `while (c) { body }` | Boolean condition, unit-valued body, repeated in the current local state |
| `heap b: i64[n] = initial { success } else { failure }` | Fixed-length initialized owner visible only in success; both branches have the same ordinary result type |
| `b.length`, `b[index]` | Bare resource name; length is `i64`, reads check the signed index before loading |
| `b[index] = value;` | Owner/edit permission; index guard precedes the integer RHS |
| `fn f(read b: i64[], x: T) -> U` / `f(read b, x)` | One optional first call-scoped view, with matching read/edit mode |
| `{ statements; final_expression }` | Lexical scope; omitted final expression has type `unit` |
| `if c { a } else { b }` | `c: bool`; both branches have the same type |
| Arithmetic | `+`, `-`, `*`, `/`, `%`, and unary `-`, on `i64` only |
| Comparison | `<`, `<=`, `>`, `>=` on `i64`; `==`, `!=` on two values of the same type/tuple shape |
| Boolean operations | `!`, short-circuit `&&`, and short-circuit `||` |
| Expression statement | Evaluate an expression, discard its result, retain its trap behavior |

An executable's root file contains exactly one `fn main() -> i64`. Other functions may return any supported scalar or flat-tuple type. Every loaded function body is checked, including unreachable or unused functions. Duplicate function names within a file or parameter names are errors. A block rejects duplicate local binding names in that block. Inner blocks may shadow outer names. A local name shadows a same-named global function, so calling that local value is a type error.

Calls may refer to later function declarations. Arity and each argument type must match the declared signature. Function identifiers cannot be stored, returned, or passed as values in M1. That restriction is removed with the higher-order-function milestone rather than emulated with unchecked pointers.

[File modules](../../spec/modules.md) add private/public declarations and qualified
names. [Contracts](../../spec/verification.md) add mathematical-integer clauses,
type-checked and erased during ordinary execution. Their optional verifier accepts
scalar and flat-tuple code with annotated loops and acyclic calls; recursion
remains unsupported by verification.
Loop `invariant` clauses are checked as Boolean mathematical specification expressions
in the scope before the condition runs, then erased. Their truth and definedness
are not established by type checking.
Early `return`, `break`, `continue`, `for`, user-defined data,
general allocation APIs, escaping references, generics, I/O, concurrency, and source-level unsafe code
remain unsupported; they remain full-language delivery requirements.

Parameters and ordinary lets are immutable. `let mut x = x;` can make a mutable
copy of a parameter; the initializer runs before the new binding enters scope.
Assignment checks the nearest binding's mutability and exact type, so an immutable
shadow prevents assignment to an outer mutable cell. Reads and function arguments capture values without exposing storage aliases. Every loop iteration
creates fresh body locals; exiting a scope removes only its own bindings.

Flat tuples have ordered scalar field types and arity 1–8. Construction evaluates
and captures fields left to right; projection evaluates the whole base once.
Equality evaluates both same-shape operands before comparing fields. Saved tuple
values survive later whole-value replacement. Nested tuples, destructuring,
partial assignment and tuple ordering are excluded. The [flat-tuple
specification](../../spec/flat-products.md) defines the exact source, interchange,
resource and verifier boundaries; existing scalar rules below are unchanged.

## Scalar evaluation rules

Operands and function arguments evaluate left to right. A trap stops the current evaluation; no later operand is evaluated. `false && e`, `true || e`, and an unselected `if` branch do not evaluate `e`. Arithmetic never invokes undefined behavior or silently wraps.

Let `L = -9223372036854775808` and `H = 9223372036854775807`. Addition, subtraction, multiplication, and negation first compute their mathematical result. A result outside `[L,H]` produces `ArithmeticOverflow`. Division and remainder produce `DivisionByZero` when the divisor is zero. Both produce `ArithmeticOverflow` for `L / -1` and `L % -1`. Otherwise division truncates toward zero and remainder is `a - trunc(a/b)*b`.

The canonical interchange tags for these traps are `arithmetic_overflow` and `division_by_zero`. Descriptive names in mathematical prose do not define additional trap kinds.

The lexer retains the unsigned decimal magnitude of an integer token without converting through a host signed integer. An unnegated literal must be at most `H`. The syntactic form `-9223372036854775808` is admitted as `L`; negating that value again traps. Parentheses around the positive out-of-range magnitude do not make it legal. Underscores, radix prefixes, and numeric suffixes are absent from M1.

`if` evaluates its condition and exactly one branch. `let` evaluates its initializer in the old environment, then extends the environment for subsequent statements. The initializer cannot refer to its own binding. A nested block removes its own bindings on exit while preserving updates to outer mutable locals. An expression statement still evaluates even when its value is discarded.

A program may diverge through recursion or a while loop. The reference interpreter uses a documented fuel budget and reports `resource_limit` when that budget is exhausted. This is not a language trap, proof of divergence, or proof of safety. A native stack or allocation failure is a host resource failure, outside the scalar semantics. Future verified termination claims require a separate proof.

## Typing judgments

`Sigma` maps function names to declared parameter and result types. `Gamma` maps local names to types and, in the local-state extension, immutable/mutable permissions. `Sigma; Gamma |- e => T` synthesizes a type; `Sigma; Gamma |- e <= T` checks an expected type. Checking succeeds when synthesis produces the same type in M1. Later closures use checking-directed rules.

The declarative core has these representative rules:

```text
Gamma(x) = T
------------------------ VAR
Sigma; Gamma |- x : T

Sigma; Gamma |- a : i64    Sigma; Gamma |- b : i64
------------------------------------------------ ARITH
Sigma; Gamma |- a op b : i64

Sigma; Gamma |- c : bool    Sigma; Gamma |- a : T    Sigma; Gamma |- b : T
------------------------------------------------------------------------ IF
Sigma; Gamma |- if c { a } else { b } : T

Sigma; Gamma |- e : U    Sigma; Gamma, x:U |- body : T
---------------------------------------------------- LET
Sigma; Gamma |- let x = e; body : T

Sigma(f) = (T1, ..., Tn) -> U    each Sigma; Gamma |- ai : Ti
---------------------------------------------------------- CALL
Sigma; Gamma |- f(a1, ..., an) : U
```

Arithmetic typing proves operand compatibility, not absence of overflow or division by zero. The operational model includes those traps. A preservation theorem must preserve expression type or reach a defined trap. Progress permits a value, a next step, or a defined trap for a closed well-typed term. A separate verification result can establish trap freedom under preconditions.

For the first expression-only mechanization, function calls are outside the theorem unless the proof explicitly models `Sigma`, function bodies, and substitution or environments. The compiler must not describe a whole program as formally type-safe solely because its expressions resemble the proven fragment.

## Scoped resources and views

The [owned-buffer revision](../../spec/owned-buffers.md) extends ordinary `Gamma`
with an independent newest-first resource context `R`. Entries have owner, read
or edit permission. Ordinary variables never shift a resource index; a new owner
never shifts an ordinary index. Signatures have one optional view mode plus the
ordinary parameter/result types. The complete function table is checked before
entry execution, including unused bodies and dead branches; recursion is allowed.

`heap b: i64[length] = initial { success } else { failure }` requires integer
length and initializer, and equal ordinary branch result types. Only `success`
extends `R` with the fresh owner. `.length` and indexed reads accept all resource
modes; writes require owner or edit. Owner/edit may grant read or edit, while read
may grant only read. A view is first and unique in both declaration and call, and
its declared/call mode must match. It is not an ordinary parameter or value type.

One nearest-binding source namespace prevents a resource lookup from skipping an
ordinary shadow. Resource names cannot be returned, stored or copied into tuples.
The whole-program checker separately checks annotations, IDs, names, entry shape,
allocation profiles and canonical per-function heap sites; raw syntax carries no
hidden typing proof. `HasType`, `ArgsTyped` and `WellFormedProgram` are independent
judgments, with checker-equivalence theorems in `ANL.Memory`.

Contracts and invariants remain ordinary-value expressions. Memory-bearing
`verify` reports unsupported before external tools run. The current memory proof
is finite machine safety and scoped loan/cleanup preservation, not a solver proof
of user heap contracts. General moves, aggregate borrows and escaping lifetimes
below remain planned extensions.

## Complete-language typing direction

Generic parameters are explicit and universally quantified at declaration boundaries. Generic bodies are checked under those abstract parameters. Local lets do not introduce implicit polymorphism. Overload resolution uses explicit trait bounds and rejects ambiguous calls. Nominal data types prevent accidental representation-based interchange.

ADT matching must cover every constructor. Guards do not establish coverage unless there is an unconditional covering pattern. A match over an owned non-`Copy` value consumes it, while a borrowed match binds borrowed fields. Partial moves and drop flags require an explicit extension to the ownership analysis before acceptance.

Closures contain typed capture records. Captures distinguish copy, move, shared borrow, and exclusive borrow. A closure's invocation permission depends on how it uses those captures. Escaping closures cannot retain references to expired stack storage. Higher-order APIs carry both invocation and effect requirements.

`Result<T,E>` and `Option<T>` are nominal library ADTs. Error propagation lowers to a match and ordinary cleanup. There is no unchecked exception channel hidden from a function type. A panic remains a defined aborting failure and is distinct from an expected `Result` error.

Safe conversions use named fallible or lossless operations. Any unchecked representation conversion is inside an explicit unsafe boundary with preconditions. Floating-point semantics, NaN behavior, and permitted transformations require a later normative specification; integer rules must not silently generalize to floats.

## Ownership and borrow-analysis interface

The complete-language checker carries unrestricted scalar bindings, affine resource bindings, and a loan environment. Owned values may move once. Compiler-derived `Copy` applies only when duplication introduces no owning resource, exclusive reference, or cleanup obligation. Shared references can copy their loan; exclusive references cannot copy.

`&'r T` permits reads during region `'r`; `&'r mut T` permits exclusive access. While a shared loan exists, overlapping storage cannot be mutated or moved. While an exclusive loan exists, access to overlapping storage is restricted to that loan and its active reborrows. A reborrow suspends the parent permission until the reborrow ends. A reference cannot outlive its storage.

The later general ownership implementation will extend scoped buffers with lexical regions, complete initialization, and whole-value moves. It rejects references stored in aggregates, self-referential values, partial moves, and escaping borrows until those cases have accepted rules. These are milestone restrictions, not the final data model.

The ownership pass consumes typed places and an explicit control-flow graph. It emits either diagnostics or move, loan, initialization, and cleanup facts attached to the same node and local IDs. A join retains a usable owner only if every incoming path supplies one. Back edges require a fixed point. A later pass cannot revive a moved value or ignore a live loan.

## Effects and authority

M1 has no external interaction effects. A pure M1 function can still trap or diverge. Future internal effect summaries distinguish allocation, external I/O, spawning, suspension, state access, and panic. Exported functions declare an upper bound on effects. Call effects must fit within that bound.

Effect-polymorphic higher-order APIs require a proven substitution rule; an effect variable cannot discard a callback's effects. External authority comes from opaque capability values, not an effect annotation. Unsafe code changes which proof obligations the programmer must discharge; it does not grant an operating-system capability.

## Compiler and verifier contracts

The type checker consumes the parsed module plus resolved names and produces typed expressions with stable node IDs, source spans, and explicit types. Invalid source produces structured diagnostics and no executable typed module. Diagnostics identify the expected type, actual type, primary source range, and the declaration that imposed the expectation.

Source blocks lower to nested core lets and their final expression. A discarded expression statement lowers to a fresh unnamed let, preserving its evaluation and trap behavior. An omitted final expression lowers to `Unit`. Name resolution occurs before interchange export. If the exporter uses de Bruijn indices, every inserted discard binding shifts later references; conformance tests must cover a discarded expression between a binding and its later use.

The verifier consumes checked and ownership-valid IR, never untyped parser output. Its mathematical integer model includes range obligations for machine arithmetic. Each obligation identifies the source node and the assumptions used. A successful solver result applies only to the named obligation and its assumptions.

Required evidence before M1 acceptance includes positive execution examples, negative type and name-resolution cases, arithmetic boundary tests, short-circuit tests, call and recursion tests, source-position diagnostics, and checked formal artifacts for the advertised theorem scope. Later milestones add compile-fail ownership tests and independent review of every unsafe abstraction.
