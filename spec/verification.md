# Scalar function contract verification

Status: implemented pure and loop-free local-state verification. Production
results are solver-trusted; the [proof inventory](../formal/PROOFS.md) records
separate model coverage and remaining correspondence obligations. Pure programs
retain executable revision `m1-2026-11-16` and report schema `apl-verify-v0`.
Local-state programs use executable revision `local-state-2026-11-17`, report
schema `apl-verify-v1`, and verification revision `apl-state-verify-v1`. The
[loop-free state contract](loop-verification.md#loop-free-report-contract)
defines the exact v1 fields. While loops remain unsupported.

## Source contracts

Function declarations can contain preconditions and postconditions between the
result type and the body.

```text
fn increment(x: i64) -> i64
    requires x < 9223372036854775807;
    ensures (answer) answer == x + 1;
{
    x + 1
}
```

The grammar extension is:

```ebnf
function = [ "pub" ], "fn", identifier, "(", [ parameters ], ")",
           "->", type, { requires_clause }, { ensures_clause }, block ;
requires_clause = "requires", specification_expression, ";" ;
ensures_clause = "ensures", "(", identifier, ")",
                 specification_expression, ";" ;
```

`requires` and `ensures` are contextual words in this declaration position.
Existing functions, parameters, and local variables with those names remain
valid. Each clause must have Boolean type. A precondition can name the function's
parameters. A postcondition can also name its explicit result binder. The binder
must differ from every parameter name and is local to that clause. Body-local
names are unavailable. Multiple clauses denote conjunction.

Specification expressions contain decimal integer literals, Boolean literals,
unit, parameter names, the result binder where allowed, parentheses, and the
existing scalar unary and binary operators with their existing precedence.
Calls, blocks, local declarations, and conditional expressions are excluded in
this first specification-expression grammar. Boolean combinations can express
guarded properties. For example, `x == 0 || answer / x == 1` guards division.

Specification `i64` parameters and results are lifted to mathematical integers.
Specification arithmetic is unbounded; it does not introduce machine overflow.
Boolean and unit values retain their types. No implicit Boolean/integer conversion
exists. A specification literal can exceed the machine range, with a limit of
4096 decimal digits. Division truncates toward zero; remainder follows the
dividend's sign. Division and remainder require a nonzero divisor. Their
definedness follows left-to-right evaluation and Boolean short circuit.

Preconditions are checked for definedness in declaration order. Each earlier
true clause can guard a later clause. A clause cannot assume its own truth, or a
later clause, to establish its definedness. Postconditions are each checked under
the function's preconditions and actual returned value. One postcondition cannot
justify another's definedness; use a guarded Boolean expression within a clause.

## Compilation and coverage

Every ordinary source command parses, resolves, and type-checks the contracts.
`check` does not establish them. `eval`, `build`, and `run` erase contract
metadata and preserve existing runtime behavior, including arithmetic traps.
They do not insert dynamic precondition or postcondition checks and do not invoke
a solver. `dump-core` exports the erased executable body in the existing scalar
format for the executable revision selected by the complete checked program.
Importing that core does not recover contracts or verification evidence.

The verifier does not add `assert`, `assume`, ghost statements, or runtime
contract traps. Runtime assertions require a separate semantic revision, core
format extension, evaluator behavior, native lowering, and formal coverage.

`apl verify FILE [--solver PATH] [--timeout-ms N] [--json]` checks every function in
the complete loaded module graph, including private and unused functions. It
accepts libraries without `main`. A function without explicit contracts has
precondition `true` and no requested postcondition; arithmetic safety is still
checked. The report states the count of explicit clauses. An empty function graph
reports `not_requested` and does not succeed as a verification attempt.

The supported executable fragment contains scalar expressions, initialized
mutable locals, and assignment, with an acyclic function-call graph and no loops. The verifier checks this graph before generating
conditions. Any recursive component makes the whole verification attempt
`unsupported`, including an unused or syntactically unreachable recursive call.
This limitation applies to verification; ordinary compilation still supports
recursion. A separate preflight visits every checked function body and rejects
`while` before compiler hashing, solver discovery, and query generation. This includes unused functions and unselected branches. It
reports `unsupported` with exit 7, identifies the construct, and emits no query
obligations. Mutable state is local scalar state only. No loop, heap, ownership,
concurrency, or foreign-call property is covered. A later loop verifier needs a
symbolic-state invariant rule covering initialization, preservation, condition and body trap
freedom, and exit postconditions. Finite unrolling is not verification.

## Verification conditions

Verification consumes the checked program and typed contract metadata, with
resolved numeric function IDs and lexical binding indices. It never verifies
untyped parser expressions or trusts serialized acceptance flags.

For each function, `D` gives the machine range of each integer parameter, `P`
is its precondition, and `Q` is a requested postcondition. The verifier requires:

1. Defined preconditions under `D`, respecting the clause ordering above.
2. Satisfiability of `D ∧ P`. An unsatisfiable precondition is a failed
   reachability obligation, never useful verification success.
3. `D ∧ P ⇒ wp(body, true)` for trap freedom and call preconditions.
4. `D ∧ P ⇒ wp(body, defined(Q) ∧ Q)` for each postcondition.

`wp` is a structurally computed weakest-precondition transformation. Its rules
evaluate local bindings and operands in source order. It substitutes resolved
values without variable capture. For example:

```text
wp(value, Q)                 = Q(value)
wp(let a in b, Q)            = wp(a, λv. wp(b[v], Q))
wp(if c then a else b, Q)    = wp(c, λv.
                                (v ⇒ wp(a, Q)) ∧ (¬v ⇒ wp(b, Q)))
wp(a + b, Q)                = wp(a, λx. wp(b, λy.
                                in_i64(x + y) ∧ Q(x + y)))
```

Short-circuit conjunction and disjunction guard the second operand. Discarded
expressions still contribute all their safety obligations. Every executed
addition, subtraction, multiplication, and negation checks its intermediate
result against `[-2^63, 2^63-1]`. Runtime division and remainder both require a
nonzero divisor and exclude the pair `(-2^63, -1)`. A final in-range answer does
not excuse an overflowing intermediate operation.

Calls evaluate actual arguments from left to right, require the callee's
preconditions on those values, and inline the callee's actual body in a fresh
parameter environment. Postconditions are never assumed as summaries. Thus an
incorrect, unverified, or contradictory callee specification cannot certify a
caller. All function bodies and clauses receive their own checks as well.

The loop-free state generator retains a symbolic value and guarded safety
formula while updating a typed environment carrying each binding's mutability.
Assignment analyzes its full right-hand side, then replaces the target's current
symbolic value. Let scope removal pops only its added binding and retains outer
updates. Immutable bindings hold value snapshots.

A conditional analyzes its condition first, then analyzes both branches from
copies of that returned state. It merges their values and environments with
conditional terms. Its safety is the condition's safety together with each
branch's safety guarded by the selected condition. Short-circuit operators merge
the right operand's state with the skipped state under the corresponding guard.
Unsafe conditions are never assumed to remove a path from the safety formula.

Calls capture each argument value immediately while passing caller state to the
next argument. Callee preconditions use these captured values. The actual callee
body is analyzed in a fresh immutable-parameter environment; its result and safety
are retained, and the caller keeps its state after argument evaluation. Callee
postconditions are not assumed. Function postconditions use the original entry
parameter symbols, independently of subsequent local state.

The implementation can share immutable expression and formula nodes to avoid
repeating continuations. It must preserve the stated `wp` rules. Named condition
records retain their function, source span, obligation kind, and exact formula.
Decomposed conditions must have the same conjunction as the complete `wp`.

## Integer encoding

SMT formulas use `Int` and `Bool`, with explicit bounds for machine values. Unit
has one value and needs no free solver variable. Formulas contain generated
numeric names, never unescaped source identifiers.

SMT-LIB integer `div` uses Euclidean division. The translation must explicitly
encode APL's truncation rule. For `b ≠ 0`:

```text
q = div(abs(a), abs(b))
trunc_div(a, b) = if (a < 0) == (b < 0) then q else -q
trunc_rem(a, b) = a - b * trunc_div(a, b)
```

Absolute values and the multiplication in this definition use mathematical
integers. Internal formulas can totalize `trunc_div(a, 0)` to zero, but a separate
guarded condition must reject every evaluated zero divisor. The totalization is
not an executable or specification result. Specification division of the machine
minimum by `-1` is mathematically valid; runtime division and remainder of those
operands trap. [SMT-LIB integer theory](https://smt-lib.org/theories-Ints.shtml),
[Z3 arithmetic](https://microsoft.github.io/z3guide/docs/theories/Arithmetic/).

## Solver protocol and limits

The first qualified solver is Z3 5.3.3. `--solver` names one executable path and
does not contain shell arguments. The default executable name is `z3`, resolved
through `PATH`. A missing or incompatible solver is an error. Solver processes
use structured arguments `-in -smt2`; no shell evaluates source or configuration.

Each query starts a fresh process. The driver disables success chatter, enables
models, declares the generated symbols, asserts the query, and requests
`check-sat`. Only the exact status atoms `sat`, `unsat`, and `unknown` are accepted.
For `sat`, the driver requests values for all non-unit input parameters in the
same solver context. It validates their names, types, uniqueness, and machine
ranges. If there are no such parameters, the model assignment is empty and the
driver omits `get-value`. It sends `exit`, requires successful process termination, and rejects
extra status tokens, solver errors, malformed replies, and trailing non-whitespace
output. An `unsat` token followed by a crash or error is not accepted.

For a validity obligation, `unsat` for its negation discharges the obligation;
`sat` supplies a candidate refutation. A reachability obligation instead expects
`sat`. Solver models remain labeled `unreplayed`; they are not presented as
confirmed runtime counterexamples. The verifier has no proof-certificate
checker or automatic counterexample replay.

`--timeout-ms` is the total wall-clock budget for solver discovery and all
queries. It defaults to 30000 and accepts integers from 1 through 600000. Each
query receives the remaining budget through Z3's timeout option, and the driver
enforces its own deadline. It kills and reaps a timed-out child. Output is drained
concurrently with input so a full pipe cannot prevent the deadline check.

The first implementation has these additional bounds:

| Resource | Limit | Outcome when exceeded |
| --- | ---: | --- |
| Expanded executable and specification expression visits | 100000 | `unknown` |
| Active expression and call expansion depth | 256 | `unknown` |
| Named solver queries | 1024 | `unknown` |
| One generated query | 1048576 bytes | `unknown` |
| Total generated query bytes | 16777216 | `unknown` |
| Solver stdout per query | 1048576 bytes | `error` |
| Solver stderr per query | 65536 bytes | `error` |

State-aware verification additionally limits the complete attempt to 1000000
symbolic work units and 100000 arena insertions. Copies, scans, and merges of
environment/context entries, variable-length formula operands, and arena
insertions are charged before allocation. Deadline checks occur during these
loops and rendering; serialized arena definitions and queries are bounded by
1 MiB. The pure v0 path retains its existing limits and query semantics.

Source-loading and parsing limits still apply. No unbounded recursive substitution
or blocking `wait_with_output` may bypass these limits. Resource exhaustion is
never evidence that a property is false or a program diverges. Z3 can return
`unknown` for nonlinear integer arithmetic; the driver preserves that result.
[Z3 parameter reference](https://microsoft.github.io/z3guide/programming/Parameters/).

## Reports and exit status

Human output gives each failed or incomplete obligation's source location and a
summary of the verified scope. `--json` emits one versioned report on stdout.
Diagnostics go to stderr. A report contains per-obligation outcomes, with this
aggregate priority when several outcomes occur:

| Aggregate | Meaning | Exit |
| --- | --- | ---: |
| `error` | Invalid source or tool failure prevents a trustworthy attempt | 1 for source; 4 for tool or I/O failure |
| `failed` | A validity query has a refuting solver model, or preconditions are unsatisfiable | 5 |
| `unsupported` | The checked program includes a feature outside the verified fragment | 7 |
| `unknown` | A solver answer, timeout, or analysis bound leaves an obligation unresolved | 6 |
| `not_requested` | The file graph contains no functions | 7 |
| `verified` | Every required obligation succeeds and every function's preconditions are satisfiable | 0 |

Parsing or source-loading resource limits retain existing exit 3. No unsupported,
unknown, failed, or empty attempt is converted to success. Preflight rejection
does not fabricate outcomes for queries that never ran. Already completed results
remain visible if a later query fails or exhausts the deadline.

The JSON report binds its schema and applicable verification revision, the
executable semantic revision, compiler
version and executable SHA-256, every loaded source path and exact-byte SHA-256,
the module/function mapping, selected scope, limits, solver executable SHA-256,
complete solver version output and arguments, each exact SMT query and its hash,
result, and any candidate model. It identifies the contract metadata as erased
by ordinary execution. Source paths are diagnostic identities, not substitutes
for content hashes.

An unsuccessful preflight report may leave tool identities null when discovery
or hashing has not run. Null means unavailable or not measured; it is not an
identity claim. Source snapshots and typed function metadata remain present when
available, and no query records are invented. The executable semantic revision
comes from the complete checked program, including stateful programs rejected
as unsupported. When source loading, parsing, or checking fails, no checked
program exists and `semantic_revision` is null in the unchanged v0 error envelope.
Checked stateful reports use v1 even when loops or recursion are unsupported,
retain `expanded_nodes: 0` on preflight failure, and add the exact scope, budget,
and complete parameter `model_symbols` fields in the loop-free state contract.
They have no loop-head or invariant metadata. A `verified` report requires all
compiler, solver, source, and query bindings above.

Every result has `trust: "smt-trusted"`. The report states that type checking ran,
tests were not run by `verify`, and dynamic contract checks were not inserted.
It claims trap freedom and requested partial-correctness properties in the
supported scope. It does not claim a checked termination proof, native compiler
correctness, or kernel-checked solver evidence.

The verifier never imports reports or reuses cached verification outcomes.
Changing any source, contract, tool, or option requires a new attempt. A saved
report describes its exact snapshot and cannot authorize a later build.

## Formal obligation and release evidence

FM-07 requires a concrete, structurally defined verification-condition generator
over a named formal syntax, with an independently defined formula semantics.
Its soundness theorem must connect valid generated conditions to the existing
program reduction relation, excluding traps and establishing postconditions for
returned values. Defining `wp` as the desired semantic property and then unfolding
that definition does not discharge this obligation.

Call-free generator soundness, acyclic inlining preservation, and the relation
between named conditions and combined `wp` are separate coverage items. Proofs
must name any omitted constructors. Even complete model proofs leave the Rust
generator, source erasure, SMT encoding, solver, and native compiler as separate
correspondence or trust obligations. The loop-free state model's continuation
generator and production's forward symbolic environment updates also require a
separate correspondence argument. The implementation must report FM-07 as open
or partial until its exact generator coverage has been independently reviewed.

Acceptance requires real solver runs for valid and false postconditions,
intermediate overflow, both division traps, signed division and remainder,
short-circuit guards, lexical shadowing, cross-file calls and failed callee
preconditions. It also requires contradictory and undefined preconditions,
recursion and loop rejection, mutation order, scope exit, branch-state merges,
argument snapshots, callee isolation, complete input models, symbolic-work limits,
missing/crashed/malformed solvers, unknown and timeout
results, input-bound tests, and a source mutation that invalidates prior evidence.
Targeted mutation tests must show that dropping an overflow check, a call
precondition, or a branch guard changes the relevant regression outcome.

Protocol fault tests may use controlled solver substitutes. They do not replace
semantic integration tests against the pinned real solver. Ordinary interpreter,
native, core-export, and formal comparison suites must continue to pass for the
erased executable bodies.
