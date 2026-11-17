# Local scalar state and while loops

Status: implemented in the interpreter, native backend, strict core interchange,
and a separate Lean local-state model. The [proof inventory](../formal/PROOFS.md)
records the model's typing, safety, finite evaluation, and embedding results;
Rust, JSON, and native correspondence remain unproved. This document specifies
initialized mutable scalar locals, assignment, and structured while statements.
The existing scalar revision `m1-2026-11-16` retains its separate proof claims.

The extension is `local-state-2026-11-17`, represented by
`apl-core-v1` and `apl-expr-v1`. Its types remain `i64`, `bool`, and `unit`.
There are no references, shared cells, escaping locals, or language heap objects.

## Source forms

```text
fn sum_to(n: i64) -> i64 {
    let mut i = 0;
    let mut sum: i64 = 0;
    while (i < n) {
        i = i + 1;
        sum = sum + i;
    }
    sum
}

fn main() -> i64 { sum_to(100) }
```

The example returns `5050`. Existing checked arithmetic applies to every
intermediate operation.

```ebnf
statement = let_statement | assignment_statement | while_statement
          | expression, ";" ;
let_statement = "let", [ "mut" ], identifier, [ ":", type ],
                "=", expression, ";" ;
assignment_statement = identifier, "=", expression, ";" ;
while_statement = "while", "(", expression, ")", block ;
```

Assignment and while are statements in this increment. A while statement ends
at its closing brace and has no trailing semicolon. Assignment requires its
semicolon. Neither form can replace an operand or a final expression. A block
containing these statements can still be an expression under the existing rules.
The while body must have type `unit`. A non-unit tail is an error; add a semicolon
to explicitly discard its value.

`mut` is contextual after `let` only when followed by a binding identifier.
`let mut = 1;` remains an immutable binding named `mut`. `while` is contextual at
a statement boundary only when its parenthesized condition is followed by a
block. A token scan finds the matching closing parenthesis before parsing the
condition. It must respect delimiter and input limits and require no speculative
AST parsing. Existing `fn while`, `while(x);`, and local identifiers named
`while` remain valid. Parentheses around a loop condition are mandatory.

## Types and scope

An initialized `let mut` has the same inference and annotation rules as `let`.
The initializer runs before the new name enters scope. Every local has a fixed
scalar type and a fixed mutability permission. Function parameters and ordinary
lets are immutable. A function can create a mutable copy of a parameter with
`let mut x = x;` in its body.

Assignment resolves the nearest lexical binding, requires it to be mutable, and
requires an exactly matching right-hand type. There are no implicit conversions,
uninitialized locals, compound assignments, chained assignments, or assignments
to qualified function names. A shadowing immutable local prevents assignment to
an outer mutable local with the same name.

Duplicate names in one block remain errors. Inner blocks may shadow outer
bindings. Leaving a block removes its new bindings and preserves changes to
outer bindings. Each loop iteration creates fresh body-local bindings. Body
locals are unavailable in the condition or after the loop.

Every function and branch is checked, including unused functions and branches
that are never selected. Type checking does not infer that a loop terminates.

## Evaluation and state

A call frame contains an ordered vector of initialized scalar values. Each
binding's immutable or mutable permission is retained in the static typing
context and checked before execution. The opaque checked program and strict
importer enforce that boundary; runtime values need no duplicate permission
flags. A local index addresses the newest value first, as in v0. Copying a local
reads its current scalar value; it does not create an alias to its storage.

An assignment evaluates its right-hand side completely, then replaces the
target cell and produces core `unit`. If the right-hand side traps, the final
replacement does not happen. Earlier mutations inside that expression are not
rolled back, although a trap terminates the whole evaluation.

All existing expressions now pass the current frame state through their
subexpressions in evaluation order. The right operand sees changes made by the
left operand. A selected branch sees changes made by its condition. A let body
sees changes made by its initializer. Short-circuit operations retain the
left operand's changes while skipping the right operand when required.

Arguments evaluate left to right in the caller's current frame. Each completed
argument is copied to an argument-value vector. Later arguments see earlier
argument mutations. The callee then receives a fresh frame containing only those
values as immutable parameters. On return, the caller resumes with its state
after all argument evaluations. Callee-local mutation cannot change caller cells.

A while evaluates its condition before each iteration. False returns core unit
without evaluating the body. True evaluates the unit body and then reevaluates
the condition in the resulting state. The final false condition's mutations are
retained. A condition or body trap stops execution. Conditions may contain blocks
that mutate outer locals; future verification rules must account for those effects.

The Rust evaluator mutates its current value vector in place. Scope exit pops
or truncates only the appended cells. It must not restore a saved vector of old
values. It must reacquire the assignment target after evaluating the right-hand
side rather than retain a host reference across vector growth.

## Fuel and native execution

Existing programs keep their existing constructor counts and depth behavior.
Each new constructor consumes one fuel unit on entry. A while constructor is
entered once; each repeated condition and body evaluation consumes its ordinary
expression fuel. The back edge itself consumes no additional unit. Thus a core
`while false { () }` needs two units and never visits its body.

The interpreter implements repetition with a host loop. If the while expression
is at depth `d`, every condition and body evaluation uses depth `d + 1` on every
iteration. Iteration does not recursively reevaluate the while constructor or
accumulate continuation frames. Nested loops and recursive calls still consume
the existing nesting budget. Every iteration evaluates at least a condition
constructor, so an infinite loop cannot evade fuel exhaustion.

Existing source, token, syntax-tree, block, JSON, and evaluator bounds remain in
force. Source assignment and while statements lower through the existing
discarded-let convention and include that let's fuel cost and index shift.

Native code has no interpreter fuel budget, as before. It uses C11 loops and
initialized lexical scalar locals. Loop control uses constant host stack space
with respect to iteration count. Calls within a loop can still recurse.
Recursion and host resource failures retain their existing limitations.
Arithmetic helpers and explicit evaluation order remain mandatory in every
build mode.

## Typed core and interchange

Keep the existing constructors and add three constructors with these exact
additional JSON fields. Every expression still includes `tag` and checked `ty`.

| Tag | Additional fields | Inferred result |
| --- | --- | --- |
| `let_mut` | `value`: EXPR, `body`: EXPR | The body type |
| `assign` | `index`: natural number, `value`: EXPR | `unit` |
| `while` | `condition`: EXPR, `body`: EXPR | `unit` |

`let_mut` extends the static and dynamic environments like `let`, but grants
assignment permission to its new binding. `assign` indexes the environment in
which its right-hand side runs. Import validates the target's existence,
mutability, and type. `while` requires a Boolean condition and unit body in the
same outer environment. All imported branches are checked before evaluation.

The v1 root and function fields are otherwise unchanged from
[core interchange v0](core-format.md). `apl-expr-v1` remains closed and call-free.
Exact-field, duplicate-member, canonical-number, scalar-range, entry, arity, and
resource validation remain unchanged. Unknown revisions and schema/revision
mismatches are errors.

The v0 importer continues to require `m1-2026-11-16` and rejects all new tags.
The v1 importer requires `local-state-2026-11-17` and accepts the old constructors
plus the three new ones. Old `let` nodes and parameters are always immutable.
No v0 field gains a new meaning.

Source export selects v0 when every checked function uses only old constructors,
and v1 when any checked function contains a new constructor. This includes unused
functions and unwritten mutable bindings. Old source exports remain unchanged.
Contracts remain erased. Reports identify the executable revision selected for
their complete checked program, not a global constant for the latest compiler.

## Structured MIR

Keep single-definition scalar `Temp` values. Add typed mutable `Slot` IDs that
are local to one function, plus these operations:

```text
MutableScope { slot: Slot, initial: Temp, body: Block } -> body.yield_type
Load(slot: Slot) -> slot.type
Store(slot: Slot, value: Temp) -> unit
While { condition: Block, body: Block } -> unit
```

The local-lowering environment distinguishes a `Temp` binding from a `Slot`
binding. Reading a mutable binding emits a load at that point in evaluation.
Its initializer lowers before `MutableScope` declares the slot. The body lowers
with that slot in scope. The scope result is a copied scalar temporary.

Validation requires unique, in-range slot definitions and matching declared,
initial, load, and store types. Slots are initialized when introduced and visible
only within their `MutableScope` body. A slot cannot escape through a function
argument or block yield; those positions contain scalar temporaries.

A loop condition block yields `bool`; its body block yields `unit`. Both can
access enclosing initialized slots. Their local temporaries and slots are
invisible to each other and after the loop. Every iteration reexecutes each
inner slot initializer. Outer slot types and initialization permissions remain
unchanged across the back edge. Validation must reject forged MIR that violates
any of these rules before C emission.

C emission declares a scope result outside a lexical block, initializes the
slot inside it, executes its body, and copies the body yield out. A loop emits
its condition block inside an actual C loop before each test, then executes the
body block only on true. Slot loads, checked operations, calls, and stores remain
separate sequenced statements. No CFG conversion, phi construction, heap box,
or address exposure is required by this increment.

## Formal model and verification boundary

The existing immutable model and its theorem inventory remain v0 artifacts.
Their continuation frames save immutable environments, so adding assignment to
those definitions without changing their state flow is unsound.

A separate `APL.LocalState` model uses configurations that carry the current value
environment on both evaluation and value return, with mutability in its typing
context. Let frames extend and then pop
scope. Conditional, binary, and argument frames consume the returned current
environment. Only a call-return frame restores a saved caller environment,
captured after all arguments have evaluated. Loop frames alternate condition
and body at bounded continuation depth. The model reuses the existing scalar
values, checked arithmetic, and trap definitions.

The extension has its own strict v1 wire adapter and executable evaluator.
Its proof inventory distinguishes these checked results:

1. Type inference agrees with a declarative judgment carrying mutability.
2. Initialized, well-typed cell environments remain well typed after assignment
   and scope removal; immutable cells cannot be changed by assignment.
3. Progress and preservation cover the new configurations, recursive calls,
   scope restoration, and loop back edges, admitting defined arithmetic traps.
4. The finite evaluator agrees with the new reduction relation. Resource
   exhaustion establishes neither divergence nor termination.
5. Finite v0 evaluator values and traps produce matching reductions and runs
   after embedding into the new model, with sufficient transition fuel. This is
   forward outcome preservation, not reverse correspondence or a divergence proof.

The model counts machine transitions, including scope and call returns. Rust
counts expression entries and separately bounds active expression nesting.
Cross-evaluator tests compare finite values and trap kinds and treat resource
exhaustion as inconclusive. These model proofs and conformance tests do not
establish Rust or compiler correspondence, termination, or arithmetic trap freedom.

`apl verify` supports loop-free `let_mut` and assignment with acyclic calls.
It rejects the complete checked program as `unsupported` when any function
contains `while` or the call graph contains recursion. This preflight runs
before solver discovery and query generation, including for unused functions
and unselected branches. It exits 7, identifies the source construct, and emits
no invented proof obligations. The existing pure verifier continues to accept
its previously supported fragment. Runtime contracts remain erased in both.

The [state verifier](loop-verification.md) carries symbolic mutable state. A later
verification increment must prove a loop-invariant rule. It needs initialization,
preservation, condition/body trap freedom, and exit-postcondition obligations over
arbitrary invariant states.
Effects in the condition belong to that rule. Finite unrolling alone cannot
justify success. A decreasing variant and termination theorem are separate work.

## Acceptance cases and exclusions

Acceptance requires agreement between source evaluation, imported v1 evaluation,
the new formal evaluator, and native execution for finite cases. Required cases
include outer mutation through a block, immutable shadowing, reinitialized loop
locals, zero and many iterations, nested loops, effectful conditions, ordered
argument mutations, isolated callee mutation, and short-circuit effects. Checked
arithmetic must trap in the same order and with the same kind in every evaluator.

Negative cases cover immutable or unknown targets, type mismatch, non-Boolean
conditions, non-unit bodies, duplicate bindings, forbidden assignment forms,
malformed v1 artifacts, and invalid MIR slot scope or initialization. Exact fuel
cases and a long finite loop must catch recursive loop interpretation. Existing
v0 source, wire fixtures, native results, proof builds, and verification tests
must continue to pass.

This increment is not full control flow. `break`, `continue`, early `return`,
labels, value-carrying loop exits, and `for` loops remain unsupported. A follow-on
control-flow increment must define abrupt outcomes, unwind only the exited
scopes, distinguish loop and call boundaries, and test those rules in Rust,
native code, interchange, and the formal model before accepting those forms.
Records and other aggregates remain a separate type-system increment.
