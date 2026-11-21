# aes-gcm 0.11.1

Theorems about the compiled machine code of `Aes128Gcm` and `Aes256Gcm` in
[aes-gcm 0.11.1](https://docs.rs/aes-gcm/0.11.1/aes_gcm/). Each theorem is about one call to a
wrapper around one of the crate's functions, and says that a well-formed call does exactly what the
specification of that function in [`Spec/`](Spec/) computes. The theorems are in
[`Statements.lean`](Statements.lean); the specifications are built on the standards in
[`Standards/`](../Standards/README.md).

## Verified operations

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| [`Aes128Gcm`](https://docs.rs/aes-gcm/0.11.1/aes_gcm/type.Aes128Gcm.html): [`AeadInOut::encrypt_in_place`](https://docs.rs/crate/aead/0.6.1/source/src/lib.rs#258) | `aes128gcm_encrypt_in_place_writes_ciphertext_and_tag_or_fails_without_room` | `GCM.ciphertextAndTag .aes128` | [SP 800-38D](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf) §7.1 |
| [`Aes128Gcm`](https://docs.rs/aes-gcm/0.11.1/aes_gcm/type.Aes128Gcm.html): [`AeadInOut::decrypt_in_place`](https://docs.rs/crate/aead/0.6.1/source/src/lib.rs#292) | `aes128gcm_decrypt_in_place_writes_plaintext_or_rejects` | `GCM.authenticPlaintextOfCiphertextWithTag .aes128` | [SP 800-38D](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf) §7.2 |
| [`Aes256Gcm`](https://docs.rs/aes-gcm/0.11.1/aes_gcm/type.Aes256Gcm.html): [`AeadInOut::encrypt_in_place`](https://docs.rs/crate/aead/0.6.1/source/src/lib.rs#258) | `aes256gcm_encrypt_in_place_writes_ciphertext_and_tag_or_fails_without_room` | `GCM.ciphertextAndTag .aes256` | [SP 800-38D](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf) §7.1 |
| [`Aes256Gcm`](https://docs.rs/aes-gcm/0.11.1/aes_gcm/type.Aes256Gcm.html): [`AeadInOut::decrypt_in_place`](https://docs.rs/crate/aead/0.6.1/source/src/lib.rs#292) | `aes256gcm_decrypt_in_place_writes_plaintext_or_rejects` | `GCM.authenticPlaintextOfCiphertextWithTag .aes256` | [SP 800-38D](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf) §7.2 |

The specifications, in [`Spec/GCM.lean`](Spec/GCM.lean), are GCM-AE and GCM-AD of
[`Standards/NIST/GCM/`](../Standards/NIST/GCM/) on bytes. They use the AES-128 or AES-256 forward
cipher of [`Standards/NIST/AES/`](../Standards/NIST/AES/) (FIPS 197-upd1) as the block cipher
`CIPH`, the 12-byte nonce as the IV, and a 128-bit tag.

Every wrapper first keys a fresh cipher with
[`KeyInit::new`](https://docs.rs/crate/aes-gcm/0.11.1/source/src/lib.rs#217)
(`src/lib.rs:217-219`) on the caller's key: AES key expansion, then the hash subkey
H = AES_K(0^128) for GHASH. So key set-up is part of every verified call, and its result is seen
only through the call's outputs.

## Theorem statements

Each theorem states that if the hypotheses below hold, the conclusion below holds. In Lean, the
hypotheses are the theorem's arguments `hCall`, `hMachine` and `hBindings`, and the conclusion is
the statement after the colon.

### Theorem Conclusions

- **The call returns, with one result.** Every successful run from the same starting state ends in
  the same final state (`UniqueExecution`).
- **The result is the specification's.** EAX is 0 (`SuccessfulStatus`) when the specification gives
  a result that fits in the buffer, and 1 (`FailureStatus`) otherwise. On success, the buffer
  (read back from final memory by `InPlace.readOutput`) starts with the specification's result:
  for an encryption the ciphertext then the tag, and for a decryption the plaintext, with the tag
  after it unchanged. `encrypt_in_place` without room for the tag returns 1 with the ciphertext
  alone in the buffer, because the crate encrypts the message before it appends the tag. When the
  specification gives `none`, the buffer is untouched.
- **The call writes nothing else.** Memory changes only in the buffer's written bytes
  (`InPlace.outputRegion`) and the stack region, and only in the stack region when the
  specification gives `none` (`MemoryWriteFrame`). `MemoryWriteFrame` bounds the final memory only,
  not the writes made during the call.
- **The caller's state is intact.** RBX, RBP and R12 to R15 (`CalleeSavedRegistersUnchanged`) and
  the clear direction flag (`DirectionFlagUnset`) are preserved, and the machine is again in a
  supported state.

Every region a valid call reads or writes ends below 4 GiB. So the message and the associated data
are shorter than 4 GiB and never exceed the crate's limits `P_MAX` (2³⁶ − 32 bytes) and `A_MAX`
(2⁶¹ − 1 bytes). The encryption specification gives `none`, the crate's `Err`, only for a length
over these limits. So no call the theorems cover reaches the encryption theorems' `none` branch, and
decryption never rejects an input for exceeding these limits.

### Theorem Hypotheses

Every theorem has three hypotheses:

- **`hCall`: the call is well formed** (`InPlace.ValidCapacityCall routine initial key nonce
  associatedData plaintext capacity` for `*_encrypt_in_place`, `InPlace.ValidCall routine initial
  key nonce associatedData sealed sealed.size sealed.size` for `*_decrypt_in_place`), with its
  arguments passed as the [calling convention](#calling-convention) describes. The two predicates'
  docstrings in [`Spec/Program.lean`](Spec/Program.lean) list every condition; in short:
  - the program loaded at its link-time addresses, RIP at the entry, the direction flag clear;
  - the length arguments matching the associated data and the buffer's contents, and the plaintext
    within the buffer's capacity;
  - every pointer nonzero, even for empty data (Rust requires this of a slice), and every region
    ending below `userAddressLimit` (2³²);
  - the routine's stack budget (`minStackBytes`: 2976 bytes for `Aes128Gcm`, 3632 for
    `Aes256Gcm`) available below RSP, and RSP 8 more than a multiple of 16;
  - the buffer disjoint from the key, nonce and associated data, and the stack region disjoint from
    all four;
  - the buffer and the stack region outside the program and the page tables; the key, nonce and
    associated data may overlap one another;
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
  - string instructions step one element at a time (the code's only string instructions are
    `rep movs` and `rep stos`);
  - the processor reports whether it supports the leading-zero-count instruction (LZCNT), which
    the instruction decoder needs to know.

### Calling convention

The theorems are about machine code, so they reference registers and memory, not Rust values. Each
verified function is reached through a small wrapper in [`program/src/lib.rs`](program/src/lib.rs),
such as `aes128gcm_encrypt_in_place` for `AeadInOut::encrypt_in_place` at `Aes128Gcm`. A wrapper is
an exported C-ABI function that builds the Rust function's arguments from its pointers and lengths,
calls it, and passes back the result. The theorems are about four wrappers, `*_encrypt_in_place`
and `*_decrypt_in_place` for each of `aes128gcm` and `aes256gcm`; their call predicates are in the
`InPlace` namespace of [`Spec/Program.lean`](Spec/Program.lean). Calls follow System V, the
standard x86-64 convention, and these four take:

| Argument | Register | Holds |
| --- | --- | --- |
| `key` | RDI | address of the key, 16 bytes for `Aes128Gcm` and 32 for `Aes256Gcm` |
| `nonce` | RSI | address of the 12-byte nonce |
| `aad` | RDX | address of the associated data |
| `aad_len` | RCX | length of the associated data |
| `buffer` | R8 | address of the buffer, read and overwritten |
| `len` | R9 | length of the buffer's contents: the plaintext, or the ciphertext followed by its tag |
| `capacity` | first stack argument | `*_encrypt_in_place` only: size of the buffer, the bytes its contents may grow to |
| return value | EAX | 0 for `Ok`, 1 for `Err` |

The wrappers pass the buffer to the crate as `SliceBuffer`, an `aead::Buffer` over the caller's
memory that `program/src/lib.rs` defines (it is not crate code). Its contents are the buffer's first
`len` bytes. Appending to it (`extend_from_slice`) fails only when the buffer has too little room,
and then writes nothing.

## Building the verified binary

The theorems are about the machine code checked in under
[`Spec/Program/Extracted/`](Spec/Program/Extracted/) (`text.bin` and `rodata.bin`). It is built
from the wrapper crate in [`program/`](program/):

```sh
cd AesGcm/program
cargo build --locked --release   # target/x86_64-unknown-none/release/libaes_gcm_program.a
```

[`scripts/extract.py`](../scripts/extract.py) runs this build with `--remap-path-prefix` flags, so
that the bytes do not depend on where the repository is checked out. It then links the library into
a fixed image with the shared [`scripts/layout.ld`](../scripts/layout.ld) and extracts `.text` and
`.rodata` with lean-x86's `x86-extract`. To reproduce the verified bytes, run from the repository
root:

```sh
bash ci/check-extraction.sh AesGcm   # rebuild, extract and compare with the checked-in files
python3 scripts/extract.py AesGcm    # rebuild and regenerate Spec/Program/Extracted/
```

This requires the following settings:

| Setting | Value |
| --- | --- |
| Compiler | Rust 1.98.1 (`program/rust-toolchain.toml`) |
| Target | `x86_64-unknown-none` at x86-64-v1 (`program/.cargo/config.toml`) |
| Layout | `scripts/layout.ld`: fixed addresses |
| Features on | `aes` |
| Features off | `alloc`, `hazmat`, `zeroize`, `getrandom`, `rand_core`, `arrayvec`, `bytes` |
| AES | aes's software backend (`--cfg aes_backend="soft"`) |
| GHASH | polyval's software backend (`--cfg polyval_backend="soft"`) |
