# md-5 0.11.0

Theorems about the compiled machine code of [md-5 0.11.0](https://docs.rs/md-5/0.11.0/md5/). Each
theorem is about one call to a wrapper that calls the crate's public methods in a fixed order, and
says that a well-formed call does exactly what RFC 1321's MD5 computes. The theorems are in
[`Statements.lean`](Statements.lean). Their specification is RFC 1321's MD5 itself, as defined in
[`Standards/RFC/MD5/`](../Standards/RFC/MD5/).

## Verified operations

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| [`Md5::digest`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.digest) | `md5_digest_writes_message_digest` | `MD5.messageDigest` | [RFC 1321 §3](https://www.rfc-editor.org/rfc/rfc1321#section-3) |
| [`Md5::new`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.new), [`Digest::update`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.update), [`Digest::finalize`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.finalize) | `md5_digest_slices_writes_message_digest` | `MD5.messageDigest` | [RFC 1321 §3](https://www.rfc-editor.org/rfc/rfc1321#section-3) |
| [`Md5::new`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.new), [`Update::update`](https://docs.rs/digest/0.11.3/digest/trait.Update.html#tymethod.update), [`FixedOutput::finalize_into`](https://docs.rs/digest/0.11.3/digest/trait.FixedOutput.html#tymethod.finalize_into) | `md5_update_finalize_into_writes_message_digest` | `MD5.messageDigest` | [RFC 1321 §3](https://www.rfc-editor.org/rfc/rfc1321#section-3) |
| [`Digest::finalize_reset`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.finalize_reset) between two messages | `md5_digest_slices_reset_writes_both_message_digests` | `MD5.messageDigest` of each | [RFC 1321 §3](https://www.rfc-editor.org/rfc/rfc1321#section-3) |
| [`Digest::finalize_into_reset`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.finalize_into_reset) between two messages | `md5_finalize_into_reset_slices_writes_both_message_digests` | `MD5.messageDigest` of each | [RFC 1321 §3](https://www.rfc-editor.org/rfc/rfc1321#section-3) |
| [`FixedOutputReset::finalize_into_reset`](https://docs.rs/digest/0.11.3/digest/trait.FixedOutputReset.html#tymethod.finalize_into_reset) between two messages | `md5_fixed_finalize_into_reset_slices_writes_both_message_digests` | `MD5.messageDigest` of each | [RFC 1321 §3](https://www.rfc-editor.org/rfc/rfc1321#section-3) |
| [`FixedOutputReset::finalize_fixed_reset`](https://docs.rs/digest/0.11.3/digest/trait.FixedOutputReset.html#method.finalize_fixed_reset) between two messages | `md5_finalize_fixed_reset_slices_writes_both_message_digests` | `MD5.messageDigest` of each | [RFC 1321 §3](https://www.rfc-editor.org/rfc/rfc1321#section-3) |
| [`Digest::reset`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.reset) between two messages | `md5_reset_slices_writes_second_message_digest` | `MD5.messageDigest` of the second | [RFC 1321 §3](https://www.rfc-editor.org/rfc/rfc1321#section-3) |
| [`Reset::reset`](https://docs.rs/digest/0.11.3/digest/trait.Reset.html#tymethod.reset) between two messages | `md5_update_reset_slices_writes_second_message_digest` | `MD5.messageDigest` of the second | [RFC 1321 §3](https://www.rfc-editor.org/rfc/rfc1321#section-3) |
| [`md5::block_api::compress`](https://docs.rs/md-5/0.11.0/md5/block_api/fn.compress.html) | `md5_compress_writes_buffer_after_blocks` | `MD5.processBlocks` | [RFC 1321 §3.4](https://www.rfc-editor.org/rfc/rfc1321#section-3.4) |

Some methods are covered only as part of a sequence. `Md5::new` is covered by each theorem whose
docstring lists it. `Default` for `Md5` is covered by those theorems and by the `Md5::digest`
theorem, since `Md5::new` and `Digest::digest` start from `Self::default()` (digest 0.11.3,
`src/digest.rs:61-63` and `127`). The two reset wrappers also call `Md5::new`, but the reset
discards its result, so their theorems say nothing about it.

## Theorem statements

Each theorem states that if the hypotheses below hold, the conclusion below holds. In Lean, the
hypotheses are the theorem's arguments `hCall`, `hMachine` and `hBindings`, and the conclusion is
the statement after the colon. Each shape of wrapper has its own call predicate for `hCall`, the
first-count shape two: `Digest.ValidCall`, `OneMessage.ValidCall`, `TwoMessages.ValidCall`,
`ResetThenDigest.ValidCall` and `Compress.ValidCall`.

### Theorem Conclusions

- **The call returns, with one result.** Every successful run from the same starting state ends in
  the same final state (`UniqueExecution`).
- **The output is the specification's.** A call cannot fail, so there is no status. The output is
  read from final memory at the initial output pointer (`readOutput`). It holds RFC 1321's digest
  of the message (`MD5.messageDigest`). For the wrappers that hash two messages, it holds the two
  digests in turn; for the wrappers that reset between them, the second message's digest alone.
  For `md5_compress`, it holds the MD buffer after the blocks (`MD5.processBlocks`).
- **The call writes nothing else.** Memory changes only in the output (for `md5_compress`, the MD
  buffer) and the stack region `[RSP − minStackBytes, RSP + 8)` (`MemoryWriteFrame`).
- **The caller's state is intact.** RBX, RBP and R12 to R15 (`CalleeSavedRegistersUnchanged`) and
  the clear direction flag (`DirectionFlagUnset`) are preserved, and the machine is again in a
  supported state (`SupportedIntegerMachineState`, `MachineRamUnitStrideDecodable`).

### Theorem Hypotheses

Every theorem has three hypotheses:

- **`hCall`: the call is well formed** (`Digest.ValidCall bindings initial input`, or the
  `ValidCall` of the wrapper's shape), with its arguments passed as the [calling
  convention](#calling-convention) describes. The docstring of `Digest.ValidCall` in
  [`Spec/Program.lean`](Spec/Program.lean) lists the conditions that every call predicate shares.
  The docstring of each other `ValidCall` adds its own separation conditions. In short:
  - RIP at the entry point, the program loaded at its link-time addresses, the direction flag
    clear;
  - every pointer nonzero, even for an empty region, including each slice address in a table, as
    Rust's `core::slice::from_raw_parts` and references require;
  - every region ending strictly below 4 GiB (`userAddressLimit`), so every slice is shorter than
    4 GiB;
  - the stack budget, `minStackBytes` bytes below RSP, and the 8-byte return slot at RSP in memory,
    with RSP 8 more than a multiple of 16;
  - the return address below 4 GiB and outside the program;
  - the stack disjoint from every input and output, and the output and the stack clear of the
    program and the page tables; the regions a call only reads may overlap one another;
  - the output free to overlap the inputs only for `md5_digest`, `md5_digest_slices`,
    `md5_update_finalize_into`, `md5_reset_slices` and `md5_update_reset_slices`, which write it
    after the last input is read;
  - no alignment except the stack's: the tables need not be eight-byte aligned and the MD buffer
    need not be four-byte aligned, although the wrappers' Rust safety contracts exclude such calls.
- **`hMachine`: the processor is in a supported state** (`SupportedIntegerMachineState`); in short:
  - 64-bit mode, with supported control-register settings and SSE enabled;
  - page tables at 0x1000 map the first 4 GiB to the same addresses (identity mapping);
  - the processor is ready to start an instruction: no interrupt or other event is pending and no
    debug trap is detected.
- **`hBindings`: memory and string instructions behave normally**
  (`MachineRamUnitStrideDecodable`):
  - no address is in the range reserved for system-management mode (SMRR), and memory below 4 GiB
    has the normal cached memory type (write-back);
  - string instructions step one element at a time (the code's only string instructions are
    `rep movs` and `rep stos`; `md5_compress` has none);
  - the processor reports whether it supports the leading-zero-count instruction (LZCNT), which
    the instruction decoder needs to know.

### Calling convention

The theorems are about machine code, so they reference registers and memory, not Rust values. Each
verified function is reached through a small wrapper in [`program/src/lib.rs`](program/src/lib.rs),
such as `md5_digest` for `Md5::digest`. Each of the 10 wrappers is an exported `extern "C"` function
that builds Rust slices from its pointer arguments, calls md-5's public methods in a fixed order,
and writes the results out as bytes. Calls follow System V, the standard x86-64 convention. The
wrappers take their arguments in four shapes, one per subsection below; the first-count shape has
two call predicates and each other shape one.

#### One-shot wrapper

`md5_digest` hashes a message in one call (`Digest.ValidCall`):

| Argument | Register | Holds |
| --- | --- | --- |
| `input` | RDI | address of the message |
| `input_len` | RSI | length of the message in bytes |
| `output` | RDX | address of a 16-byte output buffer for the digest |
| return value | none | none: the call cannot fail |

#### Slice-table wrappers

`md5_digest_slices` and `md5_update_finalize_into` hash a message given as slices
(`OneMessage.ValidCall`):

| Argument | Register | Holds |
| --- | --- | --- |
| `input` | RDI | address of a table of addresses, one per slice |
| `num_inputs` | RSI | number of slices |
| `input_lens` | RDX | address of a table of the slices' lengths |
| `output` | RCX | address of a 16-byte output buffer for the digest |
| return value | none | none: the call cannot fail |

Table entries, addresses and lengths alike, are eight-byte words. The slices, joined in order, form
the message (`Slices.message`).

#### First-count wrappers

Six wrappers take a first count, which splits the slices into two messages.
`md5_digest_slices_reset`, `md5_finalize_into_reset_slices`,
`md5_fixed_finalize_into_reset_slices` and `md5_finalize_fixed_reset_slices` hash both messages
(`TwoMessages.ValidCall`). `md5_reset_slices` and `md5_update_reset_slices` reset between them
(`ResetThenDigest.ValidCall`). All six take:

| Argument | Register | Holds |
| --- | --- | --- |
| `input` | RDI | address of a table of addresses, one per slice |
| `num_inputs` | RSI | number of slices |
| `input_lens` | RDX | address of a table of the slices' lengths |
| `num_first` | RCX | number of slices in the first message, all of them if it exceeds `num_inputs`; the rest form the second |
| `output` | R8 | address of the output buffer: 32 bytes for the two digests in turn, or, for the two reset wrappers, 16 bytes for the second message's digest |
| return value | none | none: the call cannot fail |

The tables are laid out as for the slice-table wrappers. The slices, joined in order and split by
the first count, form the two messages (`Slices.firstMessage`, `Slices.secondMessage`).

#### `compress` wrapper

`md5_compress` calls `md5::block_api::compress` (`Compress.ValidCall`):

| Argument | Register | Holds |
| --- | --- | --- |
| `state` | RDI | address of the 16-byte MD buffer, which the call reads and then overwrites |
| `blocks` | RSI | address of the blocks, 64 bytes each |
| `num_blocks` | RDX | number of blocks |
| return value | none | none: the call cannot fail |

The MD buffer holds the words A to D, each low-order byte first.

## Building the verified binary

The theorems are about the machine code checked in under
[`Spec/Program/Extracted/`](Spec/Program/Extracted/) (`text.bin` and `rodata.bin`). It is built from
the wrapper crate in [`program/`](program/):

```sh
cd Md5/program
cargo build --locked --release   # target/x86_64-unknown-none/release/libmd_5_program.a
```

[`scripts/extract.py`](../scripts/extract.py) runs this build with `--remap-path-prefix` flags, so
that the bytes do not depend on where the repository is checked out. It then links the library into
a fixed image with the shared [`scripts/layout.ld`](../scripts/layout.ld) and extracts `.text` and
`.rodata` with lean-x86's `x86-extract`. To reproduce the verified bytes, run from the repository
root:

```sh
bash ci/check-extraction.sh Md5   # rebuild, extract and compare with the checked-in files
python3 scripts/extract.py Md5    # rebuild and regenerate Spec/Program/Extracted/
```

This requires the following settings:

| Setting | Value |
| --- | --- |
| Compiler | Rust 1.98.1 (`program/rust-toolchain.toml`) |
| Target | `x86_64-unknown-none` at x86-64-v1 (`program/.cargo/config.toml`) |
| Layout | `scripts/layout.ld`: code at 0x100000, read-only data at 0x200000 |
| Features on | `oid` |
| Features off | `alloc`, `zeroize` |
| MD5 | md-5's portable backend (`--cfg md5_backend="soft"`) |
