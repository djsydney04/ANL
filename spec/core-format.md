# ANL core interchange v0

This is the M1 compiler/formal-tool contract. Its semantic revision is
`m1-2026-11-16`. It is not a compiler correctness proof.

The [local-state v1 extension](control-flow.md#typed-core-and-interchange) adds
mutable scalar locals, assignment, and while loops with semantic revision
`local-state-2026-11-17`. V0 retains exactly the fields, constructors, semantics,
and resource protocol below. A v0 document rejects the new constructors. Source
export uses v0 for scalar programs containing only these original constructors
and v1 when any checked scalar function contains a local-state constructor.
The [flat-tuple v2 extension](flat-products.md#version-selection-and-core-json)
takes precedence when any part of the checked program contains a tuple. It adds
tuple types, construction and projection without changing the v0 rules below.

The [owned-buffer v3 extension](owned-buffers.md#core-v3-interchange) takes
precedence over v0/v1/v2: any loaded heap/buffer/view form or view signature selects
`anl-core-v3`, revision `anl-owned-buffers-v1`. It adds an allocation profile,
optional view signatures, independent resource indices and canonical heap sites.
Memory-free exports keep their earlier v0/v1/v2 rules. Explicit memory-free v3
inputs are checked, but re-export may normalize them to a lower revision. V3 has
no standalone expression document. The [memory MIR](memory-mir.md) and
[evidence protocols](memory-evidence.md) define its companion interfaces.

The cumulative [word v4 extension](words.md#core-v4-and-word-mir) takes precedence
when a loaded graph uses words or a new operator/conversion. It retains explicit
v4 imports and requires an allocation profile even for pure programs. Old
schemas below keep their original allowlists and reject new word constructs.

The [boot Core envelope](boot-profile.md#core-envelope) is separate from this
hosted revision family. `anl-boot-core-v1` uses the existing ordinary word
expression encoding inside a closed target/effects/role profile, with body-free
primitive declarations and no hosted entry or allocation profile. Old readers
reject it. Its CLI import performs static checks and returns unsupported rather
than evaluating a carrier.

## Documents

A program is an object with exactly these members:

```json
{"schema":"apl-core-v0","semantic_revision":"m1-2026-11-16","functions":[],"entry":0}
```

`functions` is an ordered array. Each function is exactly
`{"id":0,"name":"main","params":[],"result":"i64","body":EXPR}`.
IDs are JSON natural numbers equal to their array index. Names are distinct ASCII
identifiers, excluding source keywords. `params` is an ordered array of type
strings, and `result` is a type string. Types are `i64`, `bool`, or `unit`.
`entry` identifies a nullary function returning `i64`; its source name need not be
`main` in an imported artifact. Source export chooses `main`.

An expression-only proof fixture is exactly
`{"schema":"apl-expr-v0","semantic_revision":"m1-2026-11-16","expression":EXPR}`.
It contains a closed expression without calls. It is distinct from a program
artifact and does not certify whole-program or recursive-call metatheory.

Objects reject missing and unknown fields. Duplicate JSON object member names are
invalid. Unknown schema/revision, constructor/operator/type, invalid numeric
representation, duplicate function names, unbound indices, invalid entry, wrong
arity, and type mismatches yield `invalid_ir`. All function bodies and branches
are checked before evaluation. A serialized `ty` is checked against inference,
never trusted. JSON number IDs and indices must be integer representations
without a fraction or exponent and fit the implementation's index range.

## Expressions

Every expression has `tag` and `ty`, plus exactly the fields in this table:

| `tag` | Additional fields |
| --- | --- |
| `integer` | `value`: canonical decimal string in signed i64 range |
| `boolean` | `value`: JSON boolean |
| `unit` | none |
| `local` | `index`: JSON natural number |
| `let` | `value`: EXPR, `body`: EXPR |
| `if` | `condition`: EXPR, `then`: EXPR, `else`: EXPR |
| `unary` | `op`: `neg` or `not`, `operand`: EXPR |
| `binary` | `op`: one of the binary operators below, `left`: EXPR, `right`: EXPR |
| `call` | `function`: function ID, `arguments`: array of EXPR |

Binary operators are `add`, `sub`, `mul`, `div`, `rem`, `lt`, `le`, `gt`, `ge`,
`eq`, `ne`, `and`, and `or`. Their typing and checked arithmetic follow
[the scalar specification](../docs/architecture/type-system.md).
Canonical decimal strings match `0|-?[1-9][0-9]*`, with no negative zero.

Local indices are zero-based de Bruijn indices. Zero means the newest binding.
At function entry, zero means the final declared parameter. A let initializer
uses the old environment; its body adds the new value at zero. Source expression
statements lower to unnamed lets and shift subsequent references. Function calls
use only their argument values as the initial callee environment.

Source spans and node IDs remain compiler metadata and are omitted from v0 JSON.
The fixed fixtures `core-program.json` and `core-expression.json` both evaluate to
`42`. The program fixture exercises a discarded let and index shifting.

## Outcomes and commands

Value outcomes are `{"outcome":"value","type":"i64","value":"42"}`,
`{"outcome":"value","type":"bool","value":true}`, or
`{"outcome":"value","type":"unit","value":null}`. Trap outcomes are
`{"outcome":"trap","trap":"arithmetic_overflow"}` or
`{"outcome":"trap","trap":"division_by_zero"}`. Resource exhaustion is
`{"outcome":"resource_limit"}`. Rejected artifacts return
`{"outcome":"invalid_ir"}`. Outcome objects contain exactly those fields.

`anl dump-core FILE` checks source, requires its executable entry, and writes a
program artifact. `anl eval-core FILE [--fuel N]` imports a program or expression
fixture, independently rechecks it, and writes one outcome JSON object. These
commands expose the interchange for conformance tooling; they do not verify
source-level correspondence. `anl eval FILE [--fuel N]` writes the signed decimal
entry result and a newline. `anl check FILE` permits a library without an entry.

Success exits 0, source/IR rejection 1, arithmetic traps 2, resource limits 3,
and invocation or infrastructure errors 4. Human diagnostics go to stderr.

## Resource protocol

`--fuel` accepts a decimal integer from 0 through 1000000000; the default is
100000. The reference evaluator has one global decreasing counter. Immediately
before evaluating any expression constructor it consumes one fuel unit. Zero
remaining fuel yields `resource_limit`. Callee bodies consume fuel normally;
entry invocation itself costs nothing. Unselected branches, skipped boolean
operands, and later operands after a trap consume no fuel. Calls evaluate
arguments left to right before the body. A discarded let consumes one unit for
the let plus the costs of its initializer and body. Negative source literals that
are admitted directly lower to a single integer constructor.

Frontends bound source and JSON files at 1048576 bytes, tokens at 100000, and
expression tree depth at 128. Parser recursion has a separate 128-level bound.
Functions, parameters, arguments, and block statements remain subject to the
same source/token/tree bounds. Evaluation nesting is limited to 256 active
expressions, independently of fuel. Importers may impose a smaller JSON nesting
limit before construction. Resource outcomes express tool limits, not a language
trap, proof of divergence, or proof of safety. A formal evaluator using a distinct
transition budget documents it separately; cross-evaluator tests compare values
and trap kinds, treating resource exhaustion as inconclusive.
