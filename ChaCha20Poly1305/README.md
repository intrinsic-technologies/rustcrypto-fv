# chacha20poly1305 0.11.0

Theorems about the compiled machine code of the `ChaCha20Poly1305` type of
[chacha20poly1305 0.11.0](https://docs.rs/chacha20poly1305/0.11.0/chacha20poly1305/). Each theorem
is about one call to a wrapper around one of the crate's functions, and says that a well-formed call
does exactly what the specification of that function in [`Spec/`](Spec/) computes. The theorems are
in [`Statements.lean`](Statements.lean); the specifications are built on the standards in
[`Standards/`](../Standards/README.md).

## Verified operations

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| [`Aead::encrypt`](https://docs.rs/crate/aead/0.6.1/source/src/lib.rs#195) | `chacha20poly1305_encrypt_writes_ciphertext_with_tag` | `AEAD.encryptWithTag` | [RFC 8439 §2.8](https://www.rfc-editor.org/rfc/rfc8439#section-2.8) |
| [`Aead::decrypt`](https://docs.rs/crate/aead/0.6.1/source/src/lib.rs#207) | `chacha20poly1305_decrypt_writes_plaintext_or_rejects_tag` | `AEAD.decryptWithTag` | [RFC 8439 §2.8](https://www.rfc-editor.org/rfc/rfc8439#section-2.8) |
| [`AeadInOut::encrypt_in_place`](https://docs.rs/crate/aead/0.6.1/source/src/lib.rs#258) | `chacha20poly1305_encrypt_in_place_writes_ciphertext_with_tag_or_rejects_buffer_without_room` | `AEAD.encryptWithTag`; `AEAD.encryptWithoutTag` without room for the tag | [RFC 8439 §2.8](https://www.rfc-editor.org/rfc/rfc8439#section-2.8) |
| [`AeadInOut::decrypt_in_place`](https://docs.rs/crate/aead/0.6.1/source/src/lib.rs#292) | `chacha20poly1305_decrypt_in_place_writes_plaintext_or_rejects_tag` | `AEAD.decryptWithTag` | [RFC 8439 §2.8](https://www.rfc-editor.org/rfc/rfc8439#section-2.8) |

Every wrapper first builds the cipher from the caller's 32-byte key with `KeyInit::new`
([`src/lib.rs:240-246`](https://docs.rs/crate/chacha20poly1305/0.11.0/source/src/lib.rs#240)),
which stores the key in the cipher. So key set-up is part of every verified call.

The specifications are in [`Spec/AEAD.lean`](Spec/AEAD.lean), built on RFC 8439 in
[`Standards/RFC/ChaCha20Poly1305/`](../Standards/RFC/ChaCha20Poly1305/): ChaCha20 (§2.4), Poly1305
(§2.5), the Poly1305 key (§2.6) and the AEAD (§2.8). `encryptWithTag` and `decryptWithTag` put the
tag after the ciphertext, in the order of RFC 8439 §2.8. `decryptWithTag` rejects an input shorter
than the tag.

## Theorem statements

Each theorem states that if the hypotheses below hold, the conclusion below holds. In Lean, the
hypotheses are the theorem's arguments `hCall`, `hMachine` and `hBindings`, and the conclusion is
the statement after the colon.

### Theorem Conclusions

- **The call returns, with one result.** Every successful run from the same starting state ends in
  the same final state (`UniqueExecution`).
- **The result is the specification's.** For a call that can fail, EAX is 0 (`SuccessfulStatus`)
  when the crate returns `Ok`, and 1 (`aeadErrorStatus`, `FailureStatus`) when it returns
  `aead::Error`. A decryption fails when the input is shorter than a tag or the tag does not match,
  and `encrypt_in_place` when the buffer has no room for the tag. `encrypt` cannot fail on inputs
  below 4 GiB, so its theorem states no status, though its wrapper returns 0. On success, the output
  (read back from final memory by `readOutput`) holds the specification's result: for an encryption
  the ciphertext followed by its 16-byte tag, and for a decryption the plaintext.
  `encrypt_in_place` without room for the tag leaves the ciphertext alone in the buffer
  (`AEAD.encryptWithoutTag`), because the crate encrypts the message before it appends the tag
  (aead 0.6.1 `src/lib.rs:276-278`). A rejected decryption leaves the output untouched.
- **The call writes nothing else.** Memory changes only in the listed regions (`MemoryWriteFrame`):
  the output (`outputRegion`), the stack, and, for `encrypt` and `decrypt`, which allocate, the heap
  bytes they allocate (`heapRegion`) and the allocator's state (`allocatorStateRegion`). A rejected
  `decrypt` still copies its input to the heap.
- **The caller's state is intact.** RBX, RBP and R12 to R15 (`CalleeSavedRegistersUnchanged`) and
  the clear direction flag (`DirectionFlagUnset`) are preserved, and the machine is again in a
  supported state.

### Theorem Hypotheses

Every theorem has three hypotheses:

- **`hCall`: the call is well formed** (`ValidCall routine initial inputs`), with its arguments
  passed as the [calling convention](#calling-convention) describes. The docstring of `ValidCall` in
  [`Spec/Program.lean`](Spec/Program.lean), with the wrapper's `Routine` from
  [`Spec/Program/Routine.lean`](Spec/Program/Routine.lean), lists every condition; in short:
  - the program loaded at its link-time addresses, RIP at the entry, the direction flag clear;
  - each length argument equal to its input's length; the heap's length argument at least what the
    call allocates, the output's length argument at least what it writes, and the capacity at least
    the message's length;
  - the inputs, the output buffer, the heap and the stack ending below `userAddressLimit` (2^32);
    no pointer needs to be nonzero except the heap's start where the call allocates (the theorems
    do not need the non-null pointers that Rust's `slice::from_raw_parts` requires);
  - the routine's stack budget (`minStackBytes`) available below RSP, and RSP 8 more than a
    multiple of 16;
  - the written regions (output, heap, allocator state, stack) pairwise disjoint, disjoint from the
    inputs and the stack arguments, and outside the program and the page tables; the inputs may
    overlap;
  - a return address below `userAddressLimit`, outside the program.
- **`hMachine`: the processor is in a supported state** (`SupportedIntegerMachineState`); in short:
  - 64-bit mode, with supported control-register settings and SSE enabled;
  - page tables at 0x1000 map the first 4 GiB to the same addresses (identity mapping);
  - the processor is ready to start an instruction: no interrupt or other event is pending and no
    debug trap is detected.
- **`hBindings`: memory and string instructions behave normally**
  (`MachineRamUnitStrideDecodable`):
  - no address is in the range reserved for system-management mode (SMRR), and memory below
    `userAddressLimit` has the normal cached memory type (write-back);
  - string instructions step one element at a time (the code's string instructions are
    `rep movs` and `rep stos`, in `memcpy`, `memset` and copies of the cipher state);
  - the processor reports whether it supports the leading-zero-count instruction (LZCNT), which
    the instruction decoder needs to know.

### Calling convention

The theorems are about machine code, so they reference registers and memory, not Rust values. Each
verified function is reached through a small wrapper in [`program/src/lib.rs`](program/src/lib.rs),
such as `chacha20poly1305_encrypt` for `Aead::encrypt`. A wrapper is an exported function that
calls one function of the crate on the cipher and writes the result out. Calls follow System V, the
standard x86-64 convention. There are two kinds of wrapper:

- **allocating wrappers** (`chacha20poly1305_encrypt`, `chacha20poly1305_decrypt`) return the result
  in an output buffer the caller supplies, using a heap the caller also supplies;
- **in-place wrappers** (`chacha20poly1305_encrypt_in_place`, `chacha20poly1305_decrypt_in_place`)
  encrypt or decrypt a buffer where it lies.

#### Allocating wrappers

The crate returns its result in a new `Vec` in the caller's heap, placed by the wrapper's bump
allocator, which hands out the heap's bytes in order from its start. The wrapper then copies the
result to the output buffer. The allocator's state is 16 bytes at 0x300000
(`allocatorStateRegion`), which a call may change.

| Argument | Register | Holds |
| --- | --- | --- |
| `key` | RDI | address of the 32-byte key |
| `nonce` | RSI | address of the 12-byte nonce |
| `associated_data` | RDX | address of the associated data |
| `message` (`ciphertext` in `decrypt`) | RCX | address of the input: the plaintext, or the ciphertext followed by its tag |
| `heap` | R8 | address of the heap |
| `output` | R9 | address of the output buffer |
| `associated_data_len` | first stack argument | length of the associated data |
| `message_len` (`ciphertext_len`) | second stack argument | length of the input |
| `heap_len` | third stack argument | size of the heap |
| `output_len` | fourth stack argument | size of the output buffer |
| return value | EAX | 0 for `Ok`, 1 (`aeadErrorStatus`) for `aead::Error` |

`encrypt` allocates the message's length plus 16 bytes, and `decrypt` the input's length (nothing
for an empty input), as the `heap` field of each `Routine` states.

#### In-place wrappers

Encryption appends the 16-byte tag, so the buffer needs room for it (`capacity`).

| Argument | Register | Holds |
| --- | --- | --- |
| `key` | RDI | address of the 32-byte key |
| `nonce` | RSI | address of the 12-byte nonce |
| `associated_data` | RDX | address of the associated data |
| `buffer` | RCX | address of the buffer, read and overwritten |
| `associated_data_len` | R8 | length of the associated data |
| `len` | R9 | length of the buffer's contents: the plaintext, or the ciphertext followed by its tag |
| `capacity` | first stack argument | `encrypt_in_place` only: size of the buffer |
| return value | EAX | 0 for `Ok`, 1 (`aeadErrorStatus`) for `aead::Error` |

## Building the verified binary

The theorems are about the machine code checked in under
[`Spec/Program/Extracted/`](Spec/Program/Extracted/) (`text.bin` and `rodata.bin`). It is built
from the wrapper crate in [`program/`](program/):

```sh
cd ChaCha20Poly1305/program
cargo build --locked --release   # target/x86_64-unknown-none/release/libchacha20poly1305_program.a
```

[`scripts/extract.py`](../scripts/extract.py) runs this build with `--remap-path-prefix` flags, so
that the bytes do not depend on where the repository is checked out. It then links the library into
a fixed image with `program/layout.ld` and extracts `.text` and `.rodata` with lean-x86's
`x86-extract`. To reproduce the verified bytes, run from the repository root:

```sh
# rebuild, extract and compare with the checked-in files
bash ci/check-extraction.sh ChaCha20Poly1305
# rebuild and regenerate Spec/Program/Extracted/
python3 scripts/extract.py ChaCha20Poly1305
```

This requires the following settings:

| Setting | Value |
| --- | --- |
| Compiler | Rust 1.98.1 (`program/rust-toolchain.toml`) |
| Target | `x86_64-unknown-none` at x86-64-v1 (`program/.cargo/config.toml`) |
| Layout | `program/layout.ld`: fixed addresses, with `.bss` at 0x300000 |
| Features on | `alloc` |
| Features off | `getrandom` |
| ChaCha20 | chacha20's software backend (`--cfg chacha20_backend="soft"`) |
| Poly1305 | poly1305's software backend (`--cfg poly1305_backend="soft"`) |
