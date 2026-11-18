# Explicit hardware exceptions in boot v2

`rv64-virt-sbi-v2` extends the [boot profile](boot-profile.md) with an explicit
illegal-instruction operation. The platform declaration uses
`platform rv64_virt_sbi_v2`; the CLI target uses `rv64-virt-sbi-v2`. Image layout,
stacks, devices, role signatures, ordinary types and the three mandatory setup
calls retain their v1 definitions.

## Source operation and authority

After the mandatory clear-SIE, disable-interrupts and install-handler prefix,
the boot entry may contain:

```anl
hw::illegal_instruction(machine);
```

`machine` is a required static authority selector. The operation takes no
runtime arguments. Source cannot choose its opcode, cause, fault PC or trap
value. Its ordinary type is `unit`, and its effect set is `{machine}`. That type
allows the call to appear in an ordinary expression; it does not mean a raised
exception produces a unit value or resumes the next expression.

Only the boot entry has machine authority. Helpers and both handlers cannot use
this operation, including in dead branches or unused definitions. The old
machine operations remain confined to the exact setup prefix. The new operation
cannot replace a prefix step. All subsequent expressions still undergo typing,
effect, call-target and cycle checks, and boot still requires its designated
terminal loop. Both handlers retain their existing terminal-loop shape.

Discovery visits all authored bodies in source order, including unreachable
suffixes. Repeated uses share one primitive declaration and one generated
implementation. Each call retains its own Core, MIR and generated C occurrence.
These occurrences do not assert reachability or distinct linked PCs.

## Closed interchange revisions

The new primitive operation object has exactly these fields:

```json
{"tag":"illegal_instruction","authority":0}
```

Its primitive row has empty parameters, result `unit`, effects `[0]`, and no
body. Canonical name, ID, discovery order and strict object rules are unchanged.
Nonzero authority values are rejected by static policy.

| Item | v2 identifier |
| --- | --- |
| Core schema | `anl-boot-core-v2` |
| MIR schema | `anl-boot-mir-v2` |
| Semantic revision | `anl-boot-rv64-virt-v2` |
| Ordinary semantic revision | `anl-words-v1` |
| Bundle schema | `anl-boot-bundle-v2` |
| Verification report schema | `anl-boot-verify-v2` |
| Unsupported verification revision | `anl-boot-unsupported-v2` |

The explicit Rust readers are `boot::import_core_v2` and `boot::import_pair_v2`.
The existing unsuffixed readers remain v1. A v2 document containing only old
operations is still v2. Readers do not upgrade, downgrade or convert a boot
program to a hosted executable. Pair admission still checks raw MIR and requires
equality with canonical lowering of its checked Core.

## Generated slot and exception boundary

The C translation unit declares the primitive as an ordinary external
`unsigned char` function. Calls retain their possible ABI continuations; they
receive no new nonreturn attribute or unreachable assumption. The compiler
generates one aligned global function in `entry.S`, containing `.4byte 0` and
no return, stack adjustment or handler implementation.

The emitted storage slot is four bytes. On the selected RISC-V implementation
with compressed-instruction support, its first zero halfword is a 16-bit illegal
instruction. The fault PC is the slot start. Neither the slot size nor the C
interface establishes a resumable PC at `pc + 4`. See the
[ISA instruction-length rules](https://docs.riscv.org/reference/isa/v20250508/unpriv/intro.html#base-instruction-length-encoding).

The intended fault contract distinguishes raising the exception from external
forwarding to supervisor mode. Raising records cause 2 at the selected slot;
the selected forwarding contract supplies trap value 0 and enters the declared
ANL hardware handler with `(2u64, fault_pc, 0u64)` on the terminal stack. This
contract depends on the firmware and platform. The operation alone does not
prove that firmware forwards the exception, makes progress or refrains from
resuming the interrupted program. It adds no return-from-trap operation.

The manifest's primitive row uses `artifact:"assembly"`; its range covers the
generated textual function definition in `entry.S`. This UTF-8 byte range is
neither a linked instruction address nor the four-byte machine-code extent.
Individual call origins and selected parks continue to refer to their actual
Core, MIR and C locations. The remaining bundle fields and six-file publication
rules follow [Boot bundles](boot-bundle.md).

## Current scope

Static checking, Core/MIR export and generated bundle emission are distinct from
native execution. Boot build, evaluation and contract verification remain
unsupported after static checking. `Bundle::setup_identity()` rejects every v2
bundle with the typed revision-unsupported result, including one with no illegal
operation. The existing v1 native setup analysis is not a v2 execution permit.

The independent Core reader is `anl_boot_v2_raw_probe`; the v1 reader remains
separate. See the [formal usage](../formal/README.md#boot-v2-core-static-checking)
for its explicit resource bounds and the
[proof scope](../formal/PROOFS.md#boot-v2-static-model-and-core-reader) for decoded
acceptance guarantees. It does not independently validate boot MIR.

The formal static model checks the new declaration, authority, discovery and
ordinary typing rules. Its fault data predicates cover slot bounds, input
presence, fixed payload fields and status-bit calculations. The separate
[runtime model](../formal/PROOFS.md#boot-v2-origins-transitions-and-local-coherence)
defines executable abstract transitions and their independent relational
specifications. It adds no CLI execution route or source-to-native proof.

## Formal runtime contract

The runtime retains the actual V2 program and source origins. Ordinary calls
cannot delegate primitive, role, synthetic or missing targets to the shared
ordinary machine. Raw handler entry requires a defined declaration; its typed
entry theorem separately requires well-formed V2 source, correctly typed
arguments and the initial world. Raw lookup alone does not recheck a signature.

The environment separates legacy delivery `D` from fault forwarding `F`.
Fault capture records the actual caller and a positive occurrence ordinal.
At `faultBefore`, a matching `D` is considered before advancing to commit.
Commit requires valid hardware and an installed handler; raising then records
the request, increments the ordinal and enters `faultPending`. No legacy
after-operation delivery is admitted for the illegal operation.

A valid pending request without `F` produces `blockedForwarding` with exactly
the same state. Malformed pending states instead produce `invalidState`.
Forwarding consumes `F`, saves the actual pending snapshot, and enters the
declared hardware handler with arguments `[2, fault_pc, 0]`. The ordinary-machine
environment stores those arguments in reverse order. The new terminal root has
empty continuation and resource stacks. The world, read cursor, ordinal, prior
legacy-delivery consumption, interrupt-enable register and installed handler are
retained. The status update clears SIE, copies its former value into SPIE and
sets SPP. This transition neither consults `D` nor resumes the saved caller PC.

Local coherence is preserved under explicit well-formed-program and valid-input
premises. It includes active typing, source alignment, memory, phase and stored
snapshot fields. It is weaker than execution eligibility: a coherent uninstalled
`faultBefore` state may advance to coherent `faultCommit`, where the next tick
is `invalidState`. The model does not infer dynamic handler installation merely
from the static setup prefix. Snapshot coherence does not assert event-history
provenance for fields that the snapshot does not store.

The separate conditional frame algebra covers transfers to a slot and the
maximum reservation for independent hardware and language terminal roots. Its
step, frame and root contracts remain assumptions; it does not execute the slot
or prove a Rust checker or RISC-V instruction implementation. Neither this
algebra nor local runtime preservation establishes global event histories,
progress, firmware forwarding, source-to-native correspondence or a complete OS.

ANL remains the authored language for boot policy and handlers. Compiler-generated
ABI adaptation and instruction templates are compiler mechanisms. They do not
introduce handwritten C or Rust implementations of OS functionality. Future
hardware requirements must extend ANL's capabilities and explicit boundaries.
