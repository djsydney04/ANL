.option norelax
.option norvc
.section .text.anl_boot_entry,"ax",@progbits
.balign 4
.globl anl_boot_entry
.type anl_boot_entry,@function
anl_boot_entry:
    lla sp, __anl_boot_stack_top
    andi sp, sp, -16
    tail anl_boot_f0
.size anl_boot_entry, .-anl_boot_entry
.section .text.anl_boot_hardware_entry,"ax",@progbits
.balign 4
.globl anl_boot_hardware_entry
.type anl_boot_hardware_entry,@function
anl_boot_hardware_entry:
    csrr a0, scause
    csrr a1, sepc
    csrr a2, stval
    lla sp, __anl_terminal_stack_top
    andi sp, sp, -16
    tail anl_boot_f1
.size anl_boot_hardware_entry, .-anl_boot_hardware_entry
.section .text.anl_boot_language_entry,"ax",@progbits
.balign 4
.globl anl_boot_language_entry
.type anl_boot_language_entry,@function
anl_boot_language_entry:
    andi a0, a0, 255
    lla sp, __anl_terminal_stack_top
    andi sp, sp, -16
    tail anl_boot_f2
.size anl_boot_language_entry, .-anl_boot_language_entry
.section .text.anl_boot_f13,"ax",@progbits
.balign 4
.globl anl_boot_f13
.type anl_boot_f13,@function
anl_boot_f13:
    .4byte 0
.size anl_boot_f13, .-anl_boot_f13
.section .note.GNU-stack,"",@progbits
