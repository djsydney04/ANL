# Verification of local state and loop invariants

Status: loop-free local-state verification and typed, erased loop annotations are
implemented. Invariant verification remains a proposal. This specifies two
verification increments over the existing `local-state-2026-11-17` runtime. The
[loop-free report contract](#loop-free-report-contract) describes current behavior.
The [source annotation rules](#source-annotations-and-erasure) also describe
current behavior; every annotated or unannotated loop remains unsupported by
`verify`. The loop verification rules below are not implemented. The
[proof inventory](../formal/PROOFS.md) records the separate loop-free and supporting
frame, fresh-state, and annotation-erasure model proofs. Their correspondence to
the production frontend and verifier remains unproved.

The first increment verifies loop-free mutable scalar code with acyclic calls.
The proposed second verification increment uses annotated while loops, including
conditions that change local state. Both rules target arithmetic safety and partial
correctness under the stated contracts. Production reports claim neither
termination nor native compiler correctness.

## Source annotations and erasure

Source programs can place clauses between a while condition and its body:

```text
fn count_to(n: i64) -> i64
    requires n >= 0;
    ensures (answer) answer == n;
{
    let mut i = 0;
    while (i < n)
        invariant 0 <= i && i <= n;
    {
        i = i + 1;
    }
    i
}
```

```ebnf
while_statement = "while", "(", expression, ")",
                  { invariant_clause }, block ;
invariant_clause = "invariant", spec_expression, ";" ;
```

`invariant` is contextual only in that position. Existing functions, parameters,
and locals named `invariant` remain valid. The while lookahead accepts either
`{` or contextual `invariant` after the matching `)`. Ordinary `while(x);` calls
retain their existing meaning. There is no parser backtracking or new reserved
word. Existing unannotated loops remain valid executable source.

Invariant expressions use the existing mathematical specification operators,
literal limits, division/remainder rules, and short-circuit definedness. They
have Boolean type. Their names resolve to the nearest visible binding at the
loop head, before the condition evaluates. Both immutable and mutable locals
are available, as are unshadowed parameters. Bindings introduced inside the
condition or body are unavailable. An ordinary immutable `let before = x;`
can retain an earlier value. There is no `old`, result binder, function call,
block, assignment, quantifier, or ghost declaration in an invariant expression.

Source checking validates every annotation's names and types, including in
unused functions and skipped branches. It does not evaluate clauses or prove
their truth or definedness: well-typed `false` and `1 / 0 == 0` clauses are
accepted. Mathematical integer literals allow up to 4096 decimal digits.
Ordinary execution erases annotations, without evaluating them or invoking a
solver. Adding or
changing a well-typed annotation leaves erased core output, native C, runtime
values, trap kinds, and interpreter fuel unchanged. Source hashes and physical
diagnostic positions can change when annotation text changes. The runtime core
schemas and semantic revision do not change. Core import does not recover
annotations.

The current verifier reports every loop as `unsupported`, before tool discovery,
with the existing `apl-verify-v1` / `apl-state-verify-v1` report and no obligations.
It does not report invariant truth or definedness. Unannotated loops remain valid
source. The proposed loop verification increment requires at least one invariant clause on every loop in every loaded function,
including unused functions and unselected branches. A missing clause produces
`unsupported`, exit 7, before solver discovery or query generation. An explicit
`invariant true;` is permitted, but may be too weak to prove safety or a result.

## Mutable state and function calls

Verification carries an ordered symbolic environment. Each entry denotes a
scalar value at that point in evaluation. It also retains the checked binding's
type and mutability. Resolved lexical indices remain de Bruijn indices. New
bindings and discarded statements shift them exactly as in the executable core.

Assignment first analyzes the right-hand side in the current environment, then
replaces the target entry in the returned environment. Scope exit removes only
the binding introduced by that scope. It preserves updated outer entries.
Branches merge both their result and their returned environments. The right
operand sees the left operand's state, except that a short-circuited operand
does not run. The selected branch sees its condition's state.

Calls analyze arguments left to right in the caller environment. Each completed
argument value is captured immediately. The callee receives only those values
as fresh immutable parameters. The caller environment after the final argument
is saved and restored after the callee returns. A callee's result and normal
return conditions are retained; its local mutations are discarded.

The verifier expands each actual callee body. It proves the callee's ordered
preconditions on the captured actual values. It never assumes a callee's
postconditions as a summary. Every loaded function also receives its own
contract checks. Recursive call graphs remain unsupported, including recursion
in unused code. Calls, nested loops, and argument blocks share the same state
rules; no special pure-condition restriction is introduced.

Function preconditions retain their existing policy. Each clause must be
defined over typed parameter inputs under earlier true clauses. The whole
precondition must have at least one satisfying typed input. That existential
query uses function inputs only and does not include loop invariants or require
a terminating execution.

Each requested postcondition is checked independently on normally returned
values, using the original function parameter symbols and its result binder.
Neither other postconditions nor the property currently being checked may
justify its definedness. Arithmetic safety and all invariant obligations must
also succeed before the whole function is reported as verified.

## The loop rule includes condition effects

Let `Inv(s)` mean that every invariant clause is defined and true in state `s`.
Let `P` describe the current normal control-flow path. The invariant point is
immediately before the condition, both on entry and after each completed body.

For a loop entered in symbolic environment `S`, generate these obligations:

1. Under `P`, prove every clause's definedness and truth in `S`.
2. Construct an arbitrary head environment `H`. Retain every immutable entry
   from `S`. Replace every mutable entry with a distinct fresh symbol of the same
   scalar type. Bound integer head values to the i64 range.
3. Under `P`, the head type bounds, and established `Inv(H)`, analyze the actual
   condition. Prove every executed arithmetic safety and call-precondition
   obligation. On a normal return it produces Boolean `b` and state `G`.
4. On the true path, analyze the body from `G`. Prove its executable safety
   obligations. On every normal body return in state `B`, prove each invariant
   clause is defined and true in `B`.
5. On the false path, continue after the loop with unit and state `G`.
   Check later executable operations and postconditions from that state.

Initialization and re-establishment do not assume any invariant conclusion in
the state being checked. Each clause's definedness and truth are obligations
under the incoming path facts, independently of other clauses at that point.
At the arbitrary head, the entire invariant may be assumed because initialization
and re-establishment are separately required. This is induction, not a source
`assume` operation.

Invariant definedness is required at established invariant points. It is not
required in all typed states outside the invariant. That differs from the
function-precondition definedness policy. For example, a division in an invariant
can be valid when its divisor is established as nonzero at entry and after every
normal body execution. An invariant cannot assume its own truth to hide an
undefined initialization.

The final false condition can change state, and the invariant need not hold in
that changed state. The following function's result is `4`, not `3`:

```text
fn final_test_effect() -> i64
    ensures (answer) answer == 4;
{
    let mut x = 0;
    while ({ x = x + 1; x < 4 })
        invariant 0 <= x && x <= 3;
    {}
    x
}
```

Every visible mutable head local is replaced, even when the loop does not assign
to it. This conservative rule avoids depending on an analysis of which variables
the loop changes. Use an invariant to retain a needed relation, or an immutable
binding for a value that does not change. Facts about pre-loop mutable values
refer to their old symbolic values; they must not silently constrain fresh head
symbols. A later optimization that retains selected mutable entries needs its
own soundness argument, including writes in conditions and call arguments.

Only normal paths require subsequent postconditions or invariant preservation.
All finite paths still require trap freedom, including paths that later diverge.
An empty `while (true) invariant true; {}` may verify with any postcondition,
because it never returns. The report must state that termination is not proved.
An infinite counter that eventually overflows must fail its safety obligations.
Finite unrolling and interpreter fuel exhaustion establish neither case.

## Concrete generation and solver queries

The state generator transforms syntax, rather than defining its output as the
semantic property to be proved. The loop-free increment retains the existing
`Symbolic { value, safe }` result and updates a typed symbolic environment with
binding permissions. Sequential expressions combine their safety conditions.
Branches merge returned values and environment entries with conditional terms;
their safety conditions are guarded by the evaluated branch condition. Calls
retain argument safety, callee preconditions, and expanded-body safety.

No separate normal-return path is needed in this increment: successful bounded
generation of loop-free code with acyclic calls returns normally whenever its
safety formula holds. Safety conditions remain obligations; they are not assumed
to prune counterexamples from later checks.

The loop increment extends the representation with a formula describing possible
normal returns, because a safe loop need not return. It also collects guarded
executable and invariant obligations:

```text
Flow { value: Symbol, env: List<Symbol>, path: Formula }
analyze(expr, binding_context, env, path, expansion_budget) -> Flow
```

An arithmetic operation emits its guarded safety condition before producing its
mathematical symbolic result. It does not remove unsafe states from the normal
path merely to make later conditions vacuous. A branch merges scalar entries
with a conditional term and merges normal paths with disjunction. Each branch
is analyzed under its own condition guard.

For a loop, the incoming path checks initialization. The arbitrary-head path
checks the condition and true body. The outgoing path is the condition's normal
return path conjoined with its false result, and the outgoing environment is
the condition's returned environment. Nested loops use the same transformation.
Every expansion of a source loop, including repeated inlined calls, receives
fresh symbolic head identities.

A function emits these query groups:

| Group | Required solver result |
| --- | --- |
| Each ordered function-precondition definedness check | `unsat` for its guarded negation |
| Function precondition satisfiability | `sat` for typed inputs satisfying all preconditions |
| `body_safe`, the conjunction of all guarded executable safety and call-precondition checks | `unsat` for its negation |
| Each `loop_invariant_initialized` clause and each `loop_invariant_preserved` clause | `unsat` for the guarded negation of definedness and truth |
| Each independent postcondition on normal returns | `unsat` for its guarded negation |

The body-safety group includes conditions generated inside loops and inlined
callees. Query metadata retains the constituent source locations and formulas.
Grouping must preserve exactly the conjunction of the generated checks; no
failed or ungenerated check may disappear behind a group status.

Queries remain quantifier-free SMT-LIB over mathematical `Int` and `Bool`.
Parameter and head symbols are declared constants with generated numeric names.
A validity query searches for an assignment violating an obligation; `unsat`
establishes its universal closure over those symbols, under its explicit guards.
Fresh loop symbols are not fixed to pre-loop values or selected witnesses.
The function precondition query remains existential and separate. There is no
requirement that every loop head or exit path be satisfiable.

Checked arithmetic keeps every existing machine-range and division trap
condition. Mathematical annotation arithmetic keeps only its mathematical
definedness conditions. In particular, specification division of the machine
minimum by `-1` is allowed, while the corresponding runtime operation traps.
The pinned solver and its transport protocol remain unchanged.

Existing time, expansion-depth, expression-visit, query-count, and output limits
remain. State analysis additionally permits at most 1,000,000 symbolic work
units and 100,000 arena insertions per verification attempt. Charge one work
unit for every copied, scanned, or merged environment/context entry, every
variable-length formula operand processed, and every arena insertion. Reserve
budget before bulk allocation; charge every pass rather than only the final
result. An entry visited once by a combined scan/merge costs one unit; a separate
copying pass costs another per entry. Deadline checks occur incrementally in
these loops and during arena growth and rendering. Incremental serialized
formula-definition bytes and final query bytes are both bounded by the existing
1 MiB query limit; this is size accounting, not a measured Rust heap cap.
Thus many parameters and branches
cannot bypass limits through environment copying or conditional-term growth.
These added limits do not change the pure v0 path.

The loop increment additionally limits head-symbol allocations to 4096 per
verification attempt. Each inlined occurrence counts separately. Crossing an
analysis bound returns `unknown`, never verification success. The loop-free
increment does not allocate head symbols or advertise that unused limit.

## Reports and unsupported cases

Pure v0 programs continue through the existing verifier and keep the
`apl-verify-v0` report contract and query semantics. State-aware reports use
`schema: "apl-verify-v1"`. The loop-free rules are identified separately as
`verification_revision: "apl-state-verify-v1"`; invariant-loop rules use
`verification_revision: "apl-loop-verify-v1"`. The executable semantic revision
remains a separate field and remains `local-state-2026-11-17` for these programs.

V1 reports retain exact source, tool, solver, query, and option identities and
the existing aggregate status/exit rules. The loop increment additionally
records invariant clause counts, source loop node IDs, inlined expansion IDs,
source binding identities, the fresh-symbol policy, and query grouping.
They retain `trust: "smt-trusted"`, `termination_proved: false`,
`dynamic_checks: false`, and erased-annotation status.

Counterexample requests use a per-query manifest containing every non-unit
entry parameter and, in the loop increment, relevant head symbols. The parser
checks exact names, uniqueness, scalar types, and applicable machine bounds.
Unit requires no symbol. Unrelated head symbols are not requested as if they
belonged to that obligation. Models distinguish source
inputs from abstract loop-head values. An abstract head may be unreachable and
can show only that an invariant is insufficient. All models remain unreplayed;
they are not automatically reported as concrete failing executions.

The verifier must reject recursion, missing loop annotations in the loop
increment, missing contract metadata, and any executable constructor outside its
advertised fragment. Invalid invariant names/types are source errors. Source
annotation calls, quantifiers, ghost code, assertions, assumptions, and runtime
contract checks are not added. Heap state, aggregates, references, abrupt exits,
concurrency, and foreign calls remain outside this verification increment.

## Loop-free report contract

After successful source checking, a program containing any local-state
constructor selects `apl-verify-v1` and `apl-state-verify-v1`. This includes
programs rejected for loops or recursion: the revision identifies the attempted
rules, not an accepted fragment. Programs containing only v0 constructors keep
the v0 path, including empty programs and unsupported pure recursion.

Malformed CLI options retain the existing invocation error on stderr, exit 4,
before report construction, including with `--json`. Errors returned before
`verify_file` obtains a checked program, including API timeout validation and
source checking, retain the existing v0 `source_error` envelope with
`semantic_revision: null`. That envelope has no `verification_revision`; token
spelling does not determine a checked semantic revision. Existing source,
resource, and infrastructure error exit codes remain unchanged.

Every checked-source Stage A report has these required top-level fields:

```text
schema, verification_revision, semantic_revision, status, trust, scope,
type_checked, tested, dynamic_checks, contracts_erased, limits, compiler,
solver, sources, functions, obligations, message, expanded_nodes
```

Their contract is:

- `schema` is `apl-verify-v1`, `verification_revision` is
  `apl-state-verify-v1`, and `semantic_revision` is `local-state-2026-11-17`.
  `trust` remains `smt-trusted`.
- `type_checked` and `contracts_erased` are true. `tested` and `dynamic_checks`
  are false. `status`, `message`, aggregation precedence, and exit codes retain
  their existing meanings.
- `scope` retains the existing fields `functions`, `arithmetic_safety`,
  `partial_correctness`, `termination_proved`, `model_proof`, and
  `native_correctness`, and adds `fragment: "loop_free_local_state_acyclic"`.
  The function scope is `all_loaded`; safety and partial correctness are true;
  termination and native correctness are false. These describe the requested
  checks, not a success claim when the report status is unsuccessful.
  `model_proof` is `See formal/PROOFS.md; model proofs do not certify Rust generation or SMT encoding`.
- `limits` retains `timeout_ms`, `expanded_nodes`, `expansion_depth`, `queries`,
  `query_bytes`, `total_query_bytes`, `solver_stdout_bytes`, and
  `solver_stderr_bytes`. Their values are the selected timeout, 100000, 256,
  1024, 1048576, 16777216, 1048576, and 65536, respectively. It adds
  `symbolic_work: 1000000` and `arena_nodes: 100000`, both attempt-wide ceilings.
- `compiler` and `solver` retain their existing identity object shapes and are
  null until those identities are available. `sources` and `functions` retain
  the existing complete checked-program metadata and ordering. `obligations`
  contains only attempted solver queries in the existing function/clause order.
- `expanded_nodes` is a required nonnegative integer, initially zero, counting
  expression/specification visits. It is updated after generation even on
  failure; state-work and arena charges do not inflate that counter.

Loop metadata, invariant counts, head-symbol limits, and loop subcheck metadata
are absent in Stage A, not empty placeholders. `source_error` and
`resource_limit` are also absent from this checked-source envelope; those flags
belong to the existing pre-check error envelope.

Every obligation retains these existing fields and adds required `model_symbols`:

```text
id, function_id, function, kind, location, expected_solver_status, trust,
query, query_sha256, status, query_complete, solver_status, model, message,
model_symbols
```

The allowed kinds remain `precondition_defined`, `precondition_satisfiable`,
`body_safe`, and `postcondition`. There are no loop obligation kinds in Stage A. `model_symbols`
lists every non-unit entry parameter in declaration order, even when unused in
that query. Each entry uses the actual parameter index and scalar type:

```json
{"symbol":"p0","type":"i64","origin":{"kind":"parameter","index":0}}
```

The solver request and returned model preserve the complete entry assignment.
Unit values are recovered from `parameter_types` and need no solver symbol.
Existing `params: &[Type]` rendering, `pN` model parsing, and returned parameter
model entries can remain unchanged in Stage A. Generalized head-symbol parsing
and selective inclusion are reserved for the loop increment.

Unsupported preflight retains checked source/function metadata but has null
tool identities, no obligations, and `expanded_nodes: 0`. A later discovery or
identity failure retains identities already obtained and invents no query.
Generation, transport, solver, and deadline failures retain all completed and
attempted query records, including partial transcripts and their hashes, with
the existing aggregate failure rules. Final tool identity checks remain required
for success. Exhausted generation bounds produce `unknown`, not `unsupported`.

Pure v0 reports retain their keys, statuses, exit codes, obligation order, and
query-generation semantics, with no new v1 fields. Proof-scope prose may be
corrected to distinguish proved finite-expansion model results from unproved
source-graph and production bridges. Source/core export bytes remain unchanged.
Compatibility tests normalize actual compiler identities, remaining-time SMT
timeouts, and this descriptive proof-scope text; all remaining report structure
and query semantics must agree. Literal report-byte identity across separately
built executables or elapsed-time schedules is not required.

## Formal acceptance

New generator definitions and soundness theorems belong in a separate namespace
over the existing `APL.LocalState` execution model. Annotation erasure maps to
its actual `Term`, and the theorem must mention its existing `Step`, `Steps`,
or `run`, rather than a replacement execution relation with different effects.
Existing pure VCG and local-state typing/evaluator theorems remain unchanged.

The loop-free model can reuse the existing mathematical symbolic terms and
formulas with a state-aware continuation that receives both result and returned
environment. Its bounded generator must construct a concrete formula and prove
its meaning against the actual LocalState machine. Successful generation can
establish a finite machine trace without adding a second evaluator. Public
contract theorems additionally require `WellTyped fs`,
`HasType (signatures fs) (immutable types.reverse) body resultTy`, and entry
values whose types equal `types`. Existing preservation supplies the expected
result type. A raw value-machine theorem does not establish source assignment
permission.

The production stateful `Symbolic` transformation and that model's continuation
transformation are distinct implementations. Their correspondence remains an
explicit gap, even after the model theorem and differential examples pass.
Neither the existing pure model nor this new model certifies Rust generation.

The loop increment additionally needs the forward `Flow`/normal-path extension,
annotation instantiation, fresh symbols, the syntax-directed loop generator,
and guarded-query grouping. Soundness must
establish that valid generated conditions exclude any finite reachable trap and
imply each requested property for normally returned values. It must not assume
the desired execution safety or termination result. Normal-return coverage needs
a witness extending the input-symbol interpretation to fresh symbols. Every
possible runtime head state must be representable; soundness cannot depend on
one chosen abstract head.

The loop proof uses initialization and preservation at `whileEval` and
`whileAgain`, proves condition/body safety along finite reductions, and uses
`whileFalse` with the updated environment for the continuation. Scope frames,
ordered argument frames, and `callReturn` must satisfy the same state relation.
Existing `LocalState.run_sound` and `run_complete` then transfer the result to
the actual finite evaluator. Acyclic body-expansion soundness is a separate
obligation from source call-graph validation and expansion completeness.

Acceptance of the loop-free increment requires a concrete state model generator
and its soundness result before enabling mutable-code verification success.
Acceptance of loop success additionally requires the invariant rule, fresh-head
coverage, annotation erasure, and query-grouping arguments. Model proofs leave
Rust/source/SMT correspondence, the solver, and native compilation explicitly
trusted or unproved. Records, termination proofs, and full control flow remain
delivery requirements beyond these bounded increments.
