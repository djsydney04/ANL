# Boot source and Core profile

The implemented boundary admits and exports boot programs for
`rv64-virt-sbi-v1`. It provides static checking and strict Core interchange.
Checked canonical Core/MIR pairs and complete generated source bundles are
specified in [Boot bundles](boot-bundle.md). Execution and image building remain
unavailable. See the
[boot chapter](../docs/book/boot-profile.md) for a complete source example and CLI
outcomes.

## Source profile

Exactly one `platform rv64_virt_sbi_v1 { ... }` block is the first root item.
A boot root has no imports; the loader rejects its import declarations before
reading child files. A hosted import graph cannot contain a platform block or
an effects annotation.

All declarations below are mandatory. Their declaration order is immaterial.
Extra or duplicate stacks, devices and roles are errors, including unused ones.

| Declaration | Required value |
| --- | --- |
| `image_base` | `2149580800u64` |
| `image_limit` | `1048576` |
| `stack boot_stack` | `[16384] align 16` |
| `stack terminal_stack` | `[4096] align 16` |
| `device uart0` | `at 268435456u64 size 256` |
| UART permissions | `read8 5; write8 0, 1, 2, 3, 4;` |
| `entry` | Defined `(u64,u64)->unit` function using `boot_stack` |
| `hardware_trap` | Defined `(u64,u64,u64)->unit` function using `terminal_stack` |
| `language_trap` | Defined `(u8)->unit` function using `terminal_stack` |

The three role functions are distinct and have no views. Their names are explicit
selectors, not naming conventions. Unsuffixed static naturals use canonical
decimal spelling. Suffixed `u64` literals retain ordinary word-literal spelling,
including leading zeros; their numeric values must match the selected operation.
Device permission lists are exactly the ascending lists shown.

Effects are closed sets: boot declares `{machine,uart0}`, handlers declare `{}`,
and other functions declare `{}` or `{uart0}`. The source annotation follows the
result type; omission means `{}`. Duplicates are errors. Wire sets are sorted
lists of authority IDs: machine 0 and UART 1. A call's effects must be included
in its caller's set. Ordinary calls cannot target a role function.

All definitions and branches are checked, including unused functions and
unreachable suffixes. The full call graph is acyclic. Heap/view forms are
forbidden. Ordinary scalar, word, tuple, local-state and expression typing uses
the existing language rules. Existing accepted specification clauses are checked
and erased; this profile adds no hardware specification operator.

The boot entry starts with exactly these three discarded unit calls:

1. `hw::csr_clear(machine, sstatus, 2u64)`.
2. `hw::csr_write(machine, sie, 0u64)`.
3. `hw::install_trap(machine, HANDLER)`, where `HANDLER` is the hardware role.

Their normalized Core is three nested immutable unit lets, each initialized by
the corresponding zero-argument primitive call. The rest of the boot body and
every other body forbid machine operations. A helper cannot acquire machine
authority by being called from boot.

Each handler normalizes to `let(unit, while(true, unit), unit)`. A mutable let,
extra expression or different loop body is not that handler shape. Boot must
contain a designated terminal occurrence. Search recognizes `while(true, unit)`;
for an immutable or mutable let, it searches the initializer first and then its
body. Other constructors do not establish this structural property. Ordinary
typing still checks both children, even when an earlier terminal occurrence makes
a later expression unreachable.

Source forbids declarations shadowing `hw`, `machine`, `uart0`, `boot_stack` or
`terminal_stack`, and all declared identifiers starting with `__hw_` or
`__carrier_`, including result binders. Calls to generated names are rejected.
Raw defined names obey ordinary ASCII identifier rules and the two prefix bans;
source-only selector names have no special binding role in raw Core.
`platform` and `effects` remain contextual words; hosted naming rules are unchanged.

## Primitive identity and signatures

Defined functions receive IDs in source order, starting at 0. Let their count be
N. Walk all bodies in that order, visiting a call before its arguments. Blocks
visit statements in order, then their tail; other children follow source order.
Parentheses are transparent. Discovery includes both branches and unused code,
does not expand callees, and excludes specification clauses.

A new static operation key receives the next ID from N onward; later uses of the
same key reuse it. Ordinary byte operands are not part of a key. For example,
`hw::write8(uart0, 0, hw::read8(uart0, 5))` discovers the write before the read,
even though the byte must be computed before a write could execute. Recompute
this first-use sequence from checked Core; it must match the primitive suffix
exactly. Unused and duplicate primitive rows are invalid.

| Operation object | Parameters | Result | Effects |
| --- | --- | --- | --- |
| `{"tag":"mmio_read8","region":0,"offset":5}` | `[]` | `u8` | `[1]` |
| `{"tag":"mmio_write8","region":0,"offset":K}`; K in 0..4 | `["u8"]` | `unit` | `[1]` |
| `{"tag":"io_fence","region":0}` | `[]` | `unit` | `[1]` |
| `{"tag":"csr_clear","authority":0,"register":"sstatus","mask":"2"}` | `[]` | `unit` | `[0]` |
| `{"tag":"csr_write","authority":0,"register":"sie","value":"0"}` | `[]` | `unit` | `[0]` |
| `{"tag":"install_trap","authority":0,"handler":H}`; H is the hardware role | `[]` | `unit` | `[0]` |

No other selectors, values or fields are admitted. These are typed operations
with an intended hardware interpretation; static admission does not supply an
executable device model or establish physical effects.

## Core envelope

The root object has exactly:

```text
schema, semantic_revision, ordinary_semantic_revision,
target_profile, image, stacks, devices, entries, functions
```

The schema is `anl-boot-core-v1`; its revision is `anl-boot-rv64-virt-v1` and its
ordinary semantic revision is `anl-words-v1`. There is no hosted `entry`,
`allocation_profile` or synthetic function.

`target_profile` has exactly `id:"rv64-virt-sbi-v1"`,
`generated_isa:"rv64im_zicsr"`, `abi:"lp64"`, `endianness:"little"`,
`privilege:"s"`, `translation:"bare"`, `harts:1`, `ram_base:"2147483648"`,
and `ram_bytes:134217728`. These are fixed target metadata, independent of the
host compiler's allocation profile.

`image` is `{"base":"2149580800","limit":1048576}`. `stacks` contains, in order,
`{"id":0,"name":"boot_stack","bytes":16384,"alignment":16}` and
`{"id":1,"name":"terminal_stack","bytes":4096,"alignment":16}`.
`devices` contains exactly
`{"id":0,"name":"uart0","authority":1,"base":"268435456","size":256,"read8":[5],"write8":[0,1,2,3,4]}`.

`entries` has exactly `boot`, `hardware` and `language`. Each is an object with
`function` and `stack`; the stacks are 0, 1 and 1 respectively.

`functions` contains a contiguous defined prefix followed by a primitive suffix.
Every ID equals its array index. A defined row has exactly:

```text
kind:"defined", id, name, view:null, params, result, effects, body
```

A primitive row has exactly:

```text
kind:"primitive", id, name:"__hw_ID", operation, params, result, effects
```

Primitive rows have no body or view. Parameters, results and ordinary expressions
use the existing [word Core encoding](words.md#core-v4-and-word-mir), including explicit
conversion fields and independently checked `ty` labels. Calls use the combined
signature table. Every raw body is retyped; annotations, IDs and operation
signatures are not trusted.

The internal mathematical signature adapter is not a serializable boot program.
Its synthetic entry and dummy bodies supply no device implementation. Neither
library target selection nor CLI import exposes a hosted executable carrier.
Old Core/MIR readers keep their old schemas and reject the boot envelope.
The separate boot pair API requires checked Core and its exact canonical MIR;
standalone boot MIR is never an execution or emission permit.

## Input, output and proof boundaries

Rust boot Core input is one UTF-8 JSON document, at most 1,048,576 bytes. Duplicate
decoded keys are rejected, including escaped spellings of an existing key.
Unknown or missing fields are rejected at every object boundary. Unquoted numbers
are canonical uint64 naturals: no sign, leading zero, fraction, exponent or
value above 18446744073709551615. IDs/counts/offsets/widths use those numbers.
Addresses and unsigned scalar payloads use canonical decimal strings; signed
`i64` literal strings retain their existing encoding. Decoded string contents
are checked after JSON escapes are resolved.

Raw indices are range-checked before host conversion and checked against their
actual binding table or tuple. The logical Core depth limit is 128. The Rust JSON reader separately
admits at most 127 nested containers; a 128th container is a resource limit.
Those are different bounds, so a logical depth allowance does not promise that
all such documents fit the JSON transport. Source byte/token/depth limits remain
the existing [compiler limits](../docs/getting-started.md).

The independent Lean boot Core reader uses the same original-byte and logical
limits, with a separate 1,024-container transport limit. It accepts one file path:
`formal/.lake/build/bin/anl_boot_raw_probe CORE_PATH`. Its report contains exactly
`raw_valid` and `reason`; successful static checking returns true/empty reason
and exit 0, malformed input returns false/nonempty reason and exit 1, a reader
resource limit returns exit 3, and argument or I/O failure returns exit 4.
Reasons contain at most 1,024 UTF-8 bytes before JSON escaping. A stdout failure
may leave no report or a partial report; no second JSON document is attempted.
This probe checks the envelope without evaluating primitive calls or exporting
the internal signature adapter. Rust and Lean do not have identical transport
admission: a document beyond Rust's container limit may reach Lean's schema or
static checker. See the [formal usage](../formal/README.md#boot-core-static-checking).

Export is bounded to 1,048,576 bytes including its final newline. The complete
document is materialized before stdout publication; output exhaustion writes no
JSON prefix. Write or flush failure is infrastructure status 4.

The `ANL.Boot` model characterizes the static judgment separately from its checker
and proves their agreement, admitted call/authority constraints, acyclicity,
canonical primitive use, and designated-tail properties. Its typed signature
adapter connects ordinary bodies to the existing Words typing model. These are
model results. The checked-decoder theorem additionally establishes that
`checkCoreDocument text = .ok p` holds exactly when `readCore text = .ok p` and
independent `Boot.WellFormedProgram p` hold. This theorem starts at the actual
reader result; it does not prove bytes-to-JSON parsing, the Rust source
parser/checker or I/O correct, execute hardware operations, or establish native
correctness. The [proof inventory](../formal/PROOFS.md#boot-static-model-and-core-reader)
records the exact ordinary-machine no-normal-return and static adapter scope.

Future execution must give explicit semantics to device reads/writes, fences,
CSR operations, trap delivery and handler entry. The selected first bring-up uses
external OpenSBI firmware. Generated entry/trap ABI templates do not establish
stack adequacy or target instruction/link correctness. Those qualifications and
the complete ANL-authored OS remain open.
