/*
 * The default fixed layout of scripts/layout.ld, with Rust's `.data.rel.ro` constants placed in the
 * read-only data image and `.bss` at 0x300000 for the state of the wrapper's bump allocator `HEAP`
 * and the system random source (src/arena.rs, src/abi.rs), the writable statics
 * (`P256.Spec.Program.Routines.allocatorStateRegion` and `randomSourceRegion`). `.bss` is written
 * before it is read, so it is not part of the extracted image. The image has no `.data`:
 * `precomputed-tables`, whose basepoint table was the only initialized writable static, is off
 * (`Cargo.toml`).
 */
PHDRS
{
    text PT_LOAD FLAGS(5);
    rodata PT_LOAD FLAGS(4);
    bss PT_LOAD FLAGS(6);
}
SECTIONS
{
    .text 0x100000 : { *(.text .text.*) } :text
    .rodata 0x200000 (READONLY) : {
        *(.rodata .rodata.*)
        *(.data.rel.ro .data.rel.ro.*)
        *(.got .got.*)
    } :rodata
    .bss 0x300000 (NOLOAD) : { *(.bss .bss.*) } :bss
    /DISCARD/ : { *(.eh_frame*) *(.comment) *(.note*) *(.debug*) }
}
