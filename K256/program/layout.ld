/*
 * scripts/layout.ld with `.data.rel.ro` added to the read-only data image (`core` places statically
 * relocated tables there, which the static relocation model resolves at link time), and `.bss` at
 * 0x300000 for the wrapper's bump allocator state `HEAP` (src/lib.rs), the one writable static:
 * `K256.Spec.Program.allocatorStateRegion` names it. A wrapper that allocates stores both words of
 * `HEAP` before reading them, so `.bss` is not part of the extracted image. The separate program
 * header keeps it out of the segments of the code and the read-only data. The image has no `.data`:
 * `precomputed-tables`, whose basepoint table was its only content, is off (`Cargo.toml`).
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
    /* Statically resolved function pointers are part of the fixed data image. */
    .rodata 0x200000 (READONLY) : {
        *(.rodata .rodata.*)
        *(.data.rel.ro .data.rel.ro.*)
        *(.got .got.*)
    } :rodata
    .bss 0x300000 (NOLOAD) : { *(.bss .bss.*) } :bss
    /* Named only so that the assertion below can measure it; it must stay empty. */
    .data : { *(.data .data.*) } :bss
    /DISCARD/ : { *(.eh_frame*) *(.comment) *(.note*) *(.debug*) }
}
/* No initialized writable static, which the extracted image would leave out. */
ASSERT(SIZEOF(.data) == 0, "`.data` must be empty: the extracted image does not hold it")
/* `.bss` holds the wrapper's `HEAP` alone, so its two words are at 0x300000, 16 bytes long. */
ASSERT(SIZEOF(.bss) == 0x10, "`.bss` must hold only the wrapper's 16-byte HEAP")
