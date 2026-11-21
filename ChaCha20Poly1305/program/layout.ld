/*
 * scripts/layout.ld plus one writable section: code at 0x100000, read-only data at 0x200000, and
 * the bump allocator's state (the only writable static) at 0x300000, which Spec/Program.lean names.
 */
SECTIONS
{
    .text 0x100000 : { *(.text .text.*) }
    /* Statically resolved function pointers are part of the fixed data image. */
    .rodata 0x200000 (READONLY) : { *(.rodata .rodata.*) *(.got .got.*) }
    .bss 0x300000 (NOLOAD) : { *(.bss .bss.*) *(.data .data.*) }
    /DISCARD/ : { *(.eh_frame*) *(.comment) *(.note*) *(.debug*) }
}
