# hkdf 0.13.0

Theorems about the compiled machine code of [hkdf 0.13.0](https://docs.rs/hkdf/0.13.0/hkdf/) with
HMAC-SHA-256 (`Hmac<Sha256>`): extraction through `HkdfExtract::<Sha256>` (`new`, `input_ikm`,
`finalize`), and `Hkdf::<Sha256>::new` followed by `expand`. Each theorem is about one call to a
wrapper around the crate's methods, and says that a well-formed call does exactly what the
specification in [`Spec/`](Spec/) computes. The theorems are in
[`Statements.lean`](Statements.lean); the specifications are built on the definitions in
[`Standards/`](../Standards/README.md).

## Verified operations

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| [`HkdfExtract::<Sha256>`](https://docs.rs/hkdf/0.13.0/hkdf/struct.GenericHkdfExtract.html): [`new`](https://docs.rs/hkdf/0.13.0/hkdf/struct.GenericHkdfExtract.html#method.new), [`input_ikm`](https://docs.rs/hkdf/0.13.0/hkdf/struct.GenericHkdfExtract.html#method.input_ikm), [`finalize`](https://docs.rs/hkdf/0.13.0/hkdf/struct.GenericHkdfExtract.html#method.finalize) | `hkdf_sha256_extract_writes_prk_of_salt_and_ikm` | `RFC5869.extract` | [RFC 5869 §2.2](https://www.rfc-editor.org/rfc/rfc5869#section-2.2); HMAC: [RFC 2104](https://www.rfc-editor.org/rfc/rfc2104) |
| [`Hkdf::<Sha256>`](https://docs.rs/hkdf/0.13.0/hkdf/struct.GenericHkdf.html): [`new`](https://docs.rs/hkdf/0.13.0/hkdf/struct.GenericHkdf.html#method.new), then [`expand`](https://docs.rs/hkdf/0.13.0/hkdf/struct.GenericHkdf.html#method.expand) | `hkdf_sha256_new_expand_writes_okm_or_rejects_length` | `RFC5869.expandFromPrk` of `RFC5869.extract` | [RFC 5869 §2.2–2.3](https://www.rfc-editor.org/rfc/rfc5869#section-2.2); HMAC: [RFC 2104](https://www.rfc-editor.org/rfc/rfc2104) |

The specifications are in [`Spec/RFC5869.lean`](Spec/RFC5869.lean), built on RFC 5869's HKDF in
[`Standards/RFC/HKDF.lean`](../Standards/RFC/HKDF.lean); the call semantics are in
[`Spec/Program.lean`](Spec/Program.lean). Each theorem covers the methods in its row together, as
one wrapper calls them in sequence. The crate's source is
[`src/lib.rs`](https://docs.rs/crate/hkdf/0.13.0/source/src/lib.rs).

## Theorem statements

Each theorem states that if the hypotheses below hold, the conclusion below holds. In Lean, the
hypotheses are the theorem's arguments `hCall`, `hMachine` and `hBindings`, and the conclusion is
the statement after the colon. The extraction theorem uses the call predicate `ValidExtractCall`.
The `new_expand` theorem uses `ValidDeriveKeyCall`, which also describes the `derive_key` wrappers:
`new_expand` takes its arguments in the same registers and stack slots, with the IKM in place of
`derive_key`'s secret.

### Theorem Conclusions

- **The call returns, with one result.** Every successful run from the same starting state ends in
  the same final state (`UniqueExecution`).
- **The result is the specification's.** The extraction call returns no status, and the PRK buffer
  holds the specification's PRK (`readOutput`). For `new_expand`, when the specification gives an
  OKM, EAX is 0 (`SuccessfulStatus`) and the output buffer holds that OKM. When the specification
  gives `InvalidLength`, an output longer than 8160 bytes, EAX is `invalidLengthStatus`
  (`FailureStatus`). The `match` arm for the specification's `InvalidPrkLength` is `False`:
  `new_expand` cannot reach that error, since extraction gives a 32-byte PRK.
- **The call writes nothing else.** Memory changes only in the output buffer and the stack region,
  and only in the stack region when the call rejects its input (`MemoryWriteFrame`).
- **The caller's state is intact.** RBX, RBP and R12 to R15 (`CalleeSavedRegistersUnchanged`) and
  the clear direction flag (`DirectionFlagUnset`) are preserved, and the machine is again in a
  supported state (`SupportedIntegerMachineState`, `MachineRamUnitStrideDecodable`).

### Theorem Hypotheses

Every theorem has three hypotheses:

- **`hCall`: the call is well formed** (`ValidExtractCall routine initial salt ikm` for extraction,
  `ValidDeriveKeyCall entryAddress minStackBytes initial salt ikm info okmLength` for `new_expand`),
  with its arguments passed as the [calling convention](#calling-convention) describes. The two
  predicates' docstrings in [`Spec/Program.lean`](Spec/Program.lean) list every condition; in short:
  - the program at its link-time addresses, RIP at the entry point, the direction flag clear;
  - each input's bytes at its address, with its length in its argument; each output buffer in RAM;
  - for `new_expand`, the info and the output buffer required only when the output length is 1 to
    8160 bytes (`255 * HashLen`, where `HashLen` is 32 for SHA-256), and for extraction, the IKM
    tables only when there is at least one slice; otherwise the code neither reads nor writes them;
  - the stack budget, `minStackBytes` bytes below RSP, and the 8-byte return slot at RSP in RAM,
    with RSP 8 more than a multiple of 16;
  - every required region, including the stack region, the return slot and the stack-argument
    slots, ending strictly below `userAddressLimit` (2^32), so the IKM tables hold fewer than 2^29
    entries;
  - the return address below 2^32 and outside the program image;
  - the output buffer and the stack region disjoint and outside the program and the page tables,
    and the stack region disjoint from the inputs;
  - the output buffer free to overlap the inputs the code reads before it writes any output (the
    salt, the IKM and, for extraction, the IKM tables), but not the info, which every output block
    reads again;
  - inputs and outputs free to lie over the stack-argument slots, which the code reads before
    writing outside the stack region and never writes;
  - conditions on the machine state only, not the wrappers' Rust contract. The code tests no
    pointer for null except `salt`, so the other buffers and the tables may be at address zero.
    No buffer or table need be aligned, and Rust's rule that a `&mut [u8]` aliases no other live
    reference is not imposed.
- **`hMachine`: the processor is in a supported state** (`SupportedIntegerMachineState`); in short:
  - 64-bit mode, with supported control-register settings and SSE enabled;
  - page tables at 0x1000 map the first 4 GiB to the same addresses (identity mapping);
  - the processor is ready to start an instruction: no interrupt or other event is pending and no
    debug trap is detected.
- **`hBindings`: memory and string instructions behave normally**
  (`MachineRamUnitStrideDecodable`):
  - no address is in the range reserved for system-management mode (SMRR), and memory below
    `userAddressLimit` has the normal cached memory type (write-back);
  - string instructions step one element at a time (the code uses the string instructions
    `rep movs` and `rep stos`);
  - the processor reports whether it supports the leading-zero-count instruction (LZCNT), which
    the instruction decoder needs to know.

### Calling convention

The theorems are about machine code, so they reference registers and memory, not Rust values. Each
verified sequence of the crate's methods is reached through a small wrapper in
[`program/src/lib.rs`](program/src/lib.rs), such as `hkdf_sha256_extract` for
`HkdfExtract::<Sha256>`'s `new`, `input_ikm` and `finalize`. Each wrapper is an exported function
that builds its HKDF state afresh from its arguments, calls the methods in sequence, writes the
result to the caller's buffer, and drops the state on return. Calls follow System V, the standard
x86-64 convention. Arguments after the sixth are stack arguments: on entry, the words at RSP + 8,
RSP + 16 and so on. A status is the low 32 bits of RAX. The subsections below give the arguments of
the two wrappers with theorems. In both, a null `salt` passes `None`, and any other address passes
`Some` of the `salt_len` bytes there.

#### `hkdf_sha256_extract`

`hkdf_sha256_extract` calls `GenericHkdfExtract::new(salt)`, `input_ikm` once per IKM slice in
order, and `finalize`, and writes the 32-byte PRK to `prk` (`ValidExtractCall`). It takes:

| Argument | Register | Holds |
| --- | --- | --- |
| `ikm` | RDI | address of a table of `num_ikm` 8-byte addresses, one per IKM slice |
| `num_ikm` | RSI | number of IKM slices |
| `ikm_lens` | RDX | address of a table of the slices' 8-byte lengths |
| `salt` | RCX | address of the salt, or 0 for no salt |
| `salt_len` | R8 | length of the salt |
| `prk` | R9 | address of the 32-byte PRK buffer |
| return value | none | none: the call cannot fail |

#### `hkdf_sha256_new_expand`

`hkdf_sha256_new_expand` calls `GenericHkdf::new(salt, ikm)`, then `expand(info, okm)`
(`ValidDeriveKeyCall`). It takes:

| Argument | Register | Holds |
| --- | --- | --- |
| `salt` | RDI | address of the salt, or 0 for no salt |
| `salt_len` | RSI | length of the salt |
| `ikm` | RDX | address of the IKM |
| `ikm_len` | RCX | length of the IKM |
| `info` | R8 | address of the info |
| `info_len` | R9 | length of the info |
| `okm` | first stack argument | address of the output buffer |
| `okm_len` | second stack argument | length of the output, the OKM |
| return value | EAX | 0 on success, 2 (`invalidLengthStatus`) on `InvalidLength` |

## Building the verified binary

The theorems are about the machine code checked in under
[`Spec/Program/Extracted/`](Spec/Program/Extracted/) (`text.bin` and `rodata.bin`). It is built
from the wrapper crate in [`program/`](program/):

```sh
cd Hkdf/program
cargo build --locked --release   # target/x86_64-unknown-none/release/libhkdf_program.a
```

[`scripts/extract.py`](../scripts/extract.py) runs this build with `--remap-path-prefix` flags, so
that the bytes do not depend on where the repository is checked out. It then links the library into
a fixed image with `program/layout.ld` and extracts `.text` and `.rodata` with lean-x86's
`x86-extract`. To reproduce the verified bytes, run from the repository root:

```sh
bash ci/check-extraction.sh Hkdf   # rebuild, extract and compare with the checked-in files
python3 scripts/extract.py Hkdf    # rebuild and regenerate Spec/Program/Extracted/
```

This requires the following settings:

| Setting | Value |
| --- | --- |
| Compiler | Rust 1.98.1 (`program/rust-toolchain.toml`) |
| Target | `x86_64-unknown-none` at x86-64-v1 (`program/.cargo/config.toml`) |
| Layout | `program/layout.ld`: `scripts/layout.ld` with `.data.rel.ro` added to the read-only data; code at 0x100000, read-only data at 0x200000 |
| Features on | `kdf` |
| Features off | default features of hkdf, sha1 and sha2 |
| SHA-1, SHA-2 | the portable compression functions of sha1 and sha2 (no backend `--cfg`) |
