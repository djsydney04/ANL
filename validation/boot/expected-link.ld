OUTPUT_FORMAT("elf64-littleriscv")
OUTPUT_ARCH(riscv)
ENTRY(anl_boot_entry)
PHDRS {
    rx PT_LOAD FLAGS(5);
    ro PT_LOAD FLAGS(4);
    rw PT_LOAD FLAGS(6);
    noexec PT_GNU_STACK FLAGS(6);
}
SECTIONS {
    . = 2149580800;
    __anl_image_start = .;
    .text.entry : { KEEP(*(.text.anl_boot_entry)) } :rx
    .text : ALIGN(4) { *(.text .text.*) } :rx
    . = ALIGN(4096);
    .rodata : ALIGN(8) { *(.rodata .rodata.* .srodata .srodata.*) } :ro
    .forbidden : {
        *(.data .data.* .sdata .sdata.* .bss .bss.* .sbss .sbss.* COMMON)
        *(.got .got.* .plt .plt.* .tdata .tdata.* .tbss .tbss.*)
        *(.init .fini .init_array .init_array.* .fini_array .fini_array.*)
        *(.preinit_array .preinit_array.* .ctors .dtors .dynamic .dynsym .dynstr)
        *(.eh_frame .eh_frame_hdr .gcc_except_table .gcc_except_table.*)
    } :NONE
    . = ALIGN(4096);
    .boot_stack (NOLOAD) : ALIGN(16) {
        __anl_boot_stack_start = .;
        . += 16384;
        __anl_boot_stack_top = .;
    } :rw
    .terminal_stack (NOLOAD) : ALIGN(16) {
        __anl_terminal_stack_start = .;
        . += 4096;
        __anl_terminal_stack_top = .;
    } :rw
    __anl_image_end = .;
    .riscv.attributes 0 : { *(.riscv.attributes) } :NONE
    .stack_sizes 0 : { KEEP(*(.stack_sizes)) } :NONE
    .debug_info 0 : { *(.debug_info .gnu.linkonce.wi.*) } :NONE
    .debug_abbrev 0 : { *(.debug_abbrev) } :NONE
    .debug_line 0 : { *(.debug_line) } :NONE
    .debug_str 0 : { *(.debug_str) } :NONE
    .debug_aranges 0 : { *(.debug_aranges) } :NONE
    .debug_ranges 0 : { *(.debug_ranges) } :NONE
    .debug_loc 0 : { *(.debug_loc) } :NONE
    .debug_frame 0 : { *(.debug_frame) } :NONE
    .debug_pubnames 0 : { *(.debug_pubnames) } :NONE
    .debug_pubtypes 0 : { *(.debug_pubtypes) } :NONE
    .debug_line_str 0 : { *(.debug_line_str) } :NONE
    .debug_addr 0 : { *(.debug_addr) } :NONE
    .debug_str_offsets 0 : { *(.debug_str_offsets) } :NONE
    .debug_rnglists 0 : { *(.debug_rnglists) } :NONE
    .debug_loclists 0 : { *(.debug_loclists) } :NONE
    .symtab 0 : { *(.symtab) } :NONE
    .strtab 0 : { *(.strtab) } :NONE
    .shstrtab 0 : { *(.shstrtab) } :NONE
    /DISCARD/ : { *(.comment .note.GNU-stack .llvm_addrsig) }
    ASSERT(anl_boot_entry == 2149580800, "ANL entry address mismatch")
    ASSERT((anl_boot_hardware_entry & 3) == 0, "ANL stvec alignment mismatch")
    ASSERT(SIZEOF(.forbidden) == 0, "ANL unsupported writable or runtime section")
    ASSERT((__anl_boot_stack_start & 15) == 0, "ANL boot stack alignment mismatch")
    ASSERT((__anl_terminal_stack_start & 15) == 0, "ANL terminal stack alignment mismatch")
    ASSERT(__anl_boot_stack_top <= __anl_terminal_stack_start, "ANL stack overlap")
    ASSERT(__anl_image_end <= 2150629376, "ANL image range exceeded")
}
