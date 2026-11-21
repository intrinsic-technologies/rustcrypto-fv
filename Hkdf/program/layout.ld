/*
 * scripts/layout.ld, with relocated read-only data in the read-only data image: code at 0x100000
 * and read-only data at 0x200000. The `expect` on the block counter in `expand_multi_info` keeps
 * the panic path, which references `core::fmt` vtables that rustc emits in `.data.rel.ro`; the
 * static link resolves them, so they are read-only data like `.rodata`.
 */
SECTIONS
{
    .text 0x100000 : { *(.text .text.*) }
    /* Statically resolved function pointers are part of the fixed data image. */
    .rodata 0x200000 (READONLY) : { *(.rodata .rodata.*) *(.data.rel.ro .data.rel.ro.*) *(.got .got.*) }
    /DISCARD/ : { *(.eh_frame*) *(.comment) *(.note*) *(.debug*) }
}
