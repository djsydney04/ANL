OUTPUT_FORMAT("elf64-littleriscv")
OUTPUT_ARCH(riscv)
ENTRY(anl_boot_entry)
SECTIONS {
    . = 2149580800;
    __anl_image_start = .;
    .text.entry : { KEEP(*(.text.anl_boot_entry)) }
    .text : ALIGN(4) { *(.text .text.*) }
    .rodata : ALIGN(8) { *(.rodata .rodata.* .srodata .srodata.*) }
    .forbidden : {
        *(.data .data.* .sdata .sdata.* .bss .bss.* .sbss .sbss.* COMMON)
        *(.got .got.* .plt .plt.* .tdata .tdata.* .tbss .tbss.*)
        *(.init .fini .init_array .init_array.* .fini_array .fini_array.*)
        *(.preinit_array .preinit_array.* .ctors .dtors .dynamic .dynsym .dynstr)
        *(.eh_frame .eh_frame_hdr .gcc_except_table .gcc_except_table.*)
    }
    .boot_stack (NOLOAD) : ALIGN(16) {
        __anl_boot_stack_start = .;
        . += 16384;
        __anl_boot_stack_top = .;
    }
    .terminal_stack (NOLOAD) : ALIGN(16) {
        __anl_terminal_stack_start = .;
        . += 4096;
        __anl_terminal_stack_top = .;
    }
    __anl_image_end = .;
    .riscv.attributes 0 : { *(.riscv.attributes) }
    /DISCARD/ : { *(.comment .note.GNU-stack .llvm_addrsig) }
    ASSERT(anl_boot_entry == 2149580800, "ANL entry address mismatch")
    ASSERT((anl_boot_hardware_entry & 3) == 0, "ANL stvec alignment mismatch")
    ASSERT(SIZEOF(.forbidden) == 0, "ANL unsupported writable or runtime section")
    ASSERT((__anl_boot_stack_start & 15) == 0, "ANL boot stack alignment mismatch")
    ASSERT((__anl_terminal_stack_start & 15) == 0, "ANL terminal stack alignment mismatch")
    ASSERT(__anl_boot_stack_top <= __anl_terminal_stack_start, "ANL stack overlap")
    ASSERT(__anl_image_end <= 2150629376, "ANL image range exceeded")
}
