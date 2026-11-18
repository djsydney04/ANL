# Unsigned words

Semantic revision `anl-words-v1` adds `u8`, `u16`, `u32` and `u64` to the
existing scalar, flat-tuple, local-state and scoped-buffer language. A word of
width `w` represents an integer from zero through `2^w - 1`.

Words work in parameters, results, recursion, modules, flat tuples, mutable
locals, branches and loops. Width is part of the type. There are no implicit
numeric conversions or literal coercions: `let x: u8 = 1;` is an error.
Executable entry remains one nullary `fn main() -> i64`.

Buffers still store `i64` cells. Lengths, indices, initializers, writes and
`.length` results remain `i64`; use explicit conversions at those boundaries.
Words are ordinary values, not addresses, references, capabilities, byte storage
or a promise about external layout. See the [book chapter](../docs/book/words.md)
for complete programs and the [buffer specification](owned-buffers.md) for
ownership and view rules.

## Literals and conversions

A word literal is decimal digits immediately followed by `u8`, `u16`, `u32` or
`u64`: `255u8`, `65535u16`, `18446744073709551615u64`. The value must fit its
written width. Source leading zeroes are allowed; exported values are canonical.
`1u8x`, `1u128`, `1_u8`, `1 u8`, radix prefixes and digit separators are invalid.
An unsuffixed integer keeps the existing `i64` rules, including the direct
negative-minimum form. Tuple projection still requires an unsuffixed single
index digit: `.0u8` is invalid.

```anl
cast u8(42)
cast i64(42u8)
truncate u8(-1)
```

`cast T(e)` preserves the mathematical integer if it fits destination `T`, and
otherwise traps with `arithmetic_overflow`. Its source and destination may be
`i64` or any word type. `truncate uw(e)` accepts the same integer sources but
only a word destination; it returns the Euclidean residue modulo `2^w`, including
for a negative `i64`. Thus `truncate u8(-1)` is `255u8`. A large `u64` is never
implicitly reinterpreted as a negative signed bit pattern. Both conversions
allow identical source/destination types and still evaluate as explicit nodes.

`cast` and `truncate` are contextual only before a complete numeric destination
and opening parenthesis. Their operand is one expression, not an argument list.
`cast(x)`, `truncate(x)`, `u8(x)` and `cast::u8(x)` remain ordinary calls.
`u8`, `u16`, `u32` and `u64` are type names only in type positions; these names
may still name functions, modules or locals. A local called `u8` does not change
`cast u8(x)`. No reserved keyword is added.

## Operators and precedence

For a particular word width, binary arithmetic, bitwise operations and
comparisons require operands of exactly that same width. Shifts are the
exception: the left operand is a word and the count is `i64`.

| Operation | Inputs | Result and failure |
| --- | --- | --- |
| `+`, `-`, `*` | Same-width words | Exact result, or `arithmetic_overflow` outside the width |
| `+%`, `-%`, `*%` | Same-width words | Sum, difference or product modulo `2^w` |
| `/`, `%` | Same-width words | Natural quotient/remainder; `division_by_zero` for zero divisor |
| `&`, `^`, `\|` | Same-width words | Bitwise and, xor, or at that width |
| `~` | One word | Width-limited complement, `2^w - 1 - value` |
| `<<`, `>>` | Word, `i64` | Logical shift; `invalid_shift` unless `0 <= count < w` |
| `<`, `<=`, `>`, `>=`, `==`, `!=` | Same-width words | Unsigned comparison returning `bool` |

Left shift returns `(value * 2^count) mod 2^w`; right shift returns
`floor(value / 2^count)`. Counts are never masked. Wrapping subtraction uses
mathematical subtraction before modulo, so `0u8 -% 1u8` is `255u8`.
Unary minus on words, signed wrapping/bitwise/shift operations, mixed widths,
Boolean numeric casts and `truncate i64(...)` are rejected.

From highest to lowest precedence:

| Level | Operators | Association |
| --- | --- | --- |
| Primary/postfix | Calls, grouping, conversions, projection | Existing postfix rules |
| Prefix | `-`, `!`, `~` | Right |
| Product | `*`, `/`, `%`, `*%` | Left |
| Sum | `+`, `-`, `+%`, `-%` | Left |
| Shift | `<<`, `>>` | Left |
| Bitwise and | `&` | Left |
| Bitwise xor | `^` | Left |
| Bitwise or | `\|` | Left |
| Relation | `<`, `<=`, `>`, `>=` | Non-associative |
| Equality | `==`, `!=` | Non-associative |
| Boolean and | `&&` | Left, short-circuit |
| Boolean or | `\|\|` | Left, short-circuit |

Operators use maximal munch; whitespace cannot split a two-character token.
`1u8 << 1 + 1` means `1u8 << (1 + 1)`; `1u8 | 2u8 == 3u8` means
`(1u8 | 2u8) == 3u8`. Repeated relations or repeated equalities still require
parentheses. No compound assignment or unary plus is introduced.

## Evaluation and traps

Each operand evaluates once, left before right, before the operation's own
range, zero-divisor or shift-count check. A left trap skips the right operand;
a right trap occurs before an outer operation check. Bitwise operations are
eager. Only existing Boolean short circuit and branch selection skip operands.

| Expression | Outcome |
| --- | --- |
| `255u8 + 1u8` | `arithmetic_overflow` |
| `255u8 +% 1u8` | `0u8` |
| `255u8 << 1` | `254u8` |
| `255u8 >> 1` | `127u8` |
| `1u8 << 8` or `1u8 >> -1` | `invalid_shift` |
| `cast u8(-1)` or `cast u8(256)` | `arithmetic_overflow` |
| `cast i64(18446744073709551615u64)` | `arithmetic_overflow` |
| `1u8 << 1u8`, `1u8 + 1`, `-0u8` | Static rejection |

`invalid_shift` is the only new semantic trap. The existing spelling is
`arithmetic_overflow`; there is no `integer_overflow` alias. Old `i64` arithmetic
is unchanged, including overflow for both `MIN / -1` and `MIN % -1`.

Memory evaluation order is unchanged: a negative length skips initialization;
a nonnegative length runs initialization before target-size rejection; a write
checks the captured resource and index before evaluating its RHS. Call arguments
are captured before granting a view, and views are revoked before restoring the
caller. New scalar operations emit no heap events. A trap retains the world and
event prefix, including live owners; host cleanup does not invent semantic
release events. Normal scope returns still close their owners.

## Core v4 and word MIR

Source graphs select `anl-core-v4`, revision `anl-words-v1`, when any loaded
function, signature, tuple field, binding type or expression uses a word or a new
operator/conversion. Unused functions and dead branches count. Even
`cast i64(1)` selects v4 before folding can erase it. Word selection precedes
buffer/product/state selection; other source graphs keep their previous rules.

The v4 root has exactly `schema`, `semantic_revision`, `allocation_profile`,
`functions`, `entry`. It reuses the [v3 function envelope](owned-buffers.md#core-v3-interchange),
independent ordinary/resource indices, canonical heap sites and executable entry
checks. Its admissible `anl-buffer-c11-v1` profile is mandatory even with no
memory forms. Profile presence does not determine word widths, link a buffer
runtime or activate tracing. Explicit word-free v4 inputs are valid and retain
v4 through evaluation, lowering and re-export. There is no v4 expression-only
document. Historical v3 normalization is unchanged.

Types add strings `u8`, `u16`, `u32`, `u64`, also allowed as flat-tuple fields.
All annotations are checked against independent inference. Added Core nodes are:

| Tag | Exact fields besides `tag`, `ty` |
| --- | --- |
| `word` | `width`, `value` |
| `convert` | `mode`, `target`, `operand` |

`width` is a JSON integer in `{8,16,32,64}`. `value` is a decimal string matching
`0|[1-9][0-9]*` and fitting that width. Signs, leading zeroes, fractions,
exponents, suffixes and negative zero are invalid; no signed-i64 or floating-point
conversion is used to admit a word payload. `mode` is `checked` or `truncate`;
`target` is a numeric scalar type string. The inferred result must equal `ty`.

New unary operator tag: `bit_not`. New binary tags: `wrap_add`, `wrap_sub`,
`wrap_mul`, `bit_and`, `bit_xor`, `bit_or`, `shl`, `shr`. Existing arithmetic and
comparison tags gain the explicit word signatures above in v4 only.

The MIR schema is `anl-words-mir-v1`, revision `anl-words-v1`. It reuses the
[memory MIR](memory-mir.md) root, function, block, typed Temp/Slot and resource
structure. A word operation has exactly `tag,width,value`; a conversion has
`tag,mode,target,operand`, where the operand is a typed Temp. The instruction's
`destination.ty` supplies the checked result annotation; operations have no
`ty` field. Lowering preserves explicit conversions and captures operand values
in language order. The independent checker validates every body, use, join,
resource lifetime and declared count.

Old Core v0/v1/v2/v3 and old MIR schemas keep their original allowlists and reject
word types, nodes and operators anywhere, including dead or unused code. Missing,
extra, duplicate or unknown fields and malformed payloads are input rejection,
not defined program traps. Canonical pair checking compares the actual checked
MIR with the exact deterministic lowering of the actual checked Core.
See the [word tool protocols](words-evidence.md).

## Resource policy and input limits

V4 Core evaluation uses the cumulative buffer resource policy even for pure
word or explicitly word-free v4 programs: fuel defaults to 100000 and accepts
0–1000000000; active expression depth is at most 256, active slots 65536, live
cells 1048576, cumulative constructed tuple fields 1048576. Depth is checked
before entry fuel. A word literal costs one expression entry; a conversion costs
one plus its operand; a binary operation costs one plus its operands. Internal
width/range checks and bit positions add no fuel. Identity casts are not erased.

Call argument/view reservations precede arguments; let slots reserve after their
initializer. Every owner, including empty owners, reserves a descriptor. Eligible
positive allocation atomically preflights cells, descriptor and fill fuel before
creating cells. Target rejection after initialization charges no reservation or
fill; refusal refunds only cells/descriptor. Normal releases reduce live counters.
Tuple-field charges occur after field evaluation. These are tool limits, not
language traps or promises about host memory availability.

The formal runner's separate administrative budget is 0–262144. Zero budget
checks structural stopping without performing a pending allocation. A cutoff
retains the exact state/world/meter prefix and is incomplete evidence; it is not
a semantic trap or a Core/MIR equal-budget claim.

Source limits remain 1 MiB and 100000 tokens per file, 8 MiB aggregate program
bytes, 128 modules and module depth 32. Expression-tree and parser-recursion
limits are separately 128. Formal Core input is at most 1 MiB and MIR at most
8 MiB, with logical expression/block depth 128 and JSON-container depth 1024.
The Rust readers retain serde_json 1.0.154's narrower recursion boundary: they
permit 127 nested containers and reject the 128th before semantic checking,
with a Core/MIR resource-limit classification. The two readers do not admit
identical nesting envelopes; boundary-sized exports need not round-trip through
Rust. IDs remain uint64-bounded canonical JSON integers. All inputs are checked
before execution, including when fuel is zero.

## Specifications and verification

This revision adds no SMT word sort, specification operator or VCG rule.
`requires`, `ensures` and loop `invariant` clauses retain their existing language.
Every new word literal, conversion or wrapping/bitwise/shift node in a clause is
rejected structurally, including in an unselected Boolean branch. Referencing a
word-containing parameter, result or loop-head binding is rejected before
conversion to a specification type. This applies to the complete binding type:
`p.0` is rejected when `p: (i64,u8)`, even though field zero is `i64`.

Ordinary-only clauses may occur beside words: `requires true` beside a word
parameter or `invariant i >= 0` beside an unreferenced word local are allowed.
An `i64` computed from words is not tainted by a dataflow analysis. These clauses
are checked and erased during ordinary execution; their truth is not established.

Every successfully checked source graph selecting v4 makes `verify` return
`anl-verify-v5`, semantic revision `anl-words-v1`, verification revision
`anl-words-unsupported-v1`, status `unsupported`, trust `not_established`, exit 7.
This precedes obligation generation, solver discovery and native execution,
even with no clauses or mixed buffers. The report binds loaded sources/functions,
sets `type_checked:true`, `contracts_erased:true`, `compiler:null`, `solver:null`,
contains no obligations, and asserts no arithmetic safety, partial correctness,
termination or native proof. Unsupported clauses instead fail source checking.
Word-free graphs retain their existing verification behavior.

The [proof inventory](../formal/PROOFS.md#unsigned-word-model) distinguishes
primitive/static/Core/MIR execution and finite canonical simulation results
from the separate byte/JSON/IO and compiled-tool trust boundaries. No word feature
establishes source/compiler/native correctness, freestanding execution or an ANL
OS. Byte storage/layout, addresses, MMIO, atomics, interrupts and OS subsystems
remain open language work; a Rust compiler and C bootstrap helpers do not supply
those ANL-authored subsystems.
