/*
 * Default fixed layout for extracted programs: code at 0x100000 and read-only data at 0x200000.
 * scripts/extract.py passes the entry symbols with --entry and --undefined, so --gc-sections
 * keeps every configured entry. Copy this file to <Crate>/program/layout.ld to change it.
 */
SECTIONS
{
    .text 0x100000 : { *(.text .text.*) }
    /* Statically resolved function pointers are part of the fixed data image. */
    .rodata 0x200000 (READONLY) : { *(.rodata .rodata.*) *(.got .got.*) }
    /DISCARD/ : { *(.eh_frame*) *(.comment) *(.note*) *(.debug*) }
}
