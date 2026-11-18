# Terminal hardware handlers in boot v3

`rv64-virt-sbi-v3` allows the ANL hardware handler to compute and access the
declared UART before its designated terminal loop. The source declaration is
`platform rv64_virt_sbi_v3`; the CLI target is `rv64-virt-sbi-v3`.

Image layout, stack reservations, device declarations, ordinary types and role
signatures retain their [boot profile](boot-profile.md) definitions. The
[v2 illegal-instruction operation](boot-profile-v2.md) and its authority and
exception boundaries remain available. This revision adds no new primitive.

After building the compiler, check and emit the
[terminal diagnostic example](../examples/boot/terminal-hardware-handler.anl)
from the repository root:

```sh
./target/release/anl check examples/boot/terminal-hardware-handler.anl --target rv64-virt-sbi-v3
./target/release/anl emit-boot examples/boot/terminal-hardware-handler.anl --out target/boot-terminal-handler
```

The output directory must not already exist. Emission produces Core, MIR, C,
entry assembly, a linker script and a manifest; it does not link or execute an
image.

## Handler policy

The hardware role receives the three raw words `(cause, pc, value)`. Its body
may use the existing ordinary expressions, including flat tuples, local mutable
variables, conditionals and acyclic helper calls. Its effects must be empty or
exactly `{uart0}`. A UART read, write or UART-effect helper call requires that
effect, including when the call occurs in an unused branch.

The body must contain a designated terminal loop. Selection follows sequencing
in value-before-body order, including ordinary and mutable bindings. A loop
inside a conditional does not satisfy this requirement. Selecting a terminal
loop is a structural check; it does not establish that the preceding computation
terminates or reaches the loop.

The language handler still has empty effects and contains exactly its terminal
loop. The boot role still has exactly `{machine, uart0}`, starts with the three
mandatory setup operations, and contains its own designated terminal loop.
Ordinary helpers may have empty effects or `{uart0}`. Calls into any role are
forbidden. Every definition and every syntactic branch undergoes typing,
authority and cycle checks, including unused helpers and unreachable suffixes.

Hardware handlers and helpers cannot use machine operations. In particular,
they cannot install a handler, change interrupt configuration, or call
`hw::illegal_instruction(machine)`. The setup operations remain confined to the
boot prefix. Memory and view operations remain outside this profile.

## Device and exception boundaries

UART access keeps the existing static selector, byte width, permitted offsets
and fence implementations. A status read is an external observation; static
admission does not establish a device response or a completed write. The
authored example initializes the UART in ANL, selects a byte from the cause,
reads readiness once, optionally writes once, and parks. It does not decode the
faulting instruction, advance the saved PC, or return to interrupted code.

Entry adaptation remains compiler generated. It captures the raw trap words,
selects the terminal stack and transfers to the ANL role. Firmware forwarding
and device behavior are external contracts. Neither a generated bundle nor
static checking proves delivery, progress, absence of a second fault, or safe
resumption. There is no return-from-trap operation in this revision.

## Interchange and tooling

| Item | v3 identifier |
| --- | --- |
| Core schema | `anl-boot-core-v3` |
| MIR schema | `anl-boot-mir-v3` |
| Semantic revision | `anl-boot-rv64-virt-v3` |
| Ordinary semantic revision | `anl-words-v1` |
| Bundle schema | `anl-boot-bundle-v3` |
| Verification report schema | `anl-boot-verify-v3` |
| Unsupported verification revision | `anl-boot-unsupported-v3` |

The explicit Rust readers are `boot::import_core_v3` and
`boot::import_pair_v3`. Existing readers retain their original revisions.
Metadata must agree completely. Pair admission validates raw MIR and requires
equality with canonical lowering of the admitted Core. A program using only
older operations still belongs to its declared revision.

Source checking, Core/MIR export and six-file bundle emission are available.
Boot build, evaluation and contract verification remain unsupported after
static checking. Verification reports retain `trust: "not_established"`.

All three existing native identity APIs—`setup_identity`,
`exception_setup_identity` and `illegal_slot_identity`—reject v3 with their
typed revision-unsupported result, including a v3 program without an illegal
operation. Existing native analyses do not establish the broader handler's
memory, device, stack or control-flow behavior.

The OS policy and handler body are authored in ANL. Generated C and assembly
implement the compiler's translation and hardware instruction templates; they
do not supply a handwritten OS subsystem. Additional hardware requirements must
be expressed by extending ANL and documenting their semantics.

## Static model

The [Lean model](../formal/PROOFS.md#boot-v3-static-handler-policy-and-reader)
proves agreement between the V3 checker and its independent well-formedness
predicate, plus acceptance of its checked Core reader. It shares the raw V2
record representation while requiring the V3 metadata and handler policy.
These static results do not extend V2 runtime/local-coherence theorems to V3 or
establish Rust, native, firmware or device correctness.
