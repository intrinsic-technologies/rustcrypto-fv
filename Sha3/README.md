# sha3 0.12.0

Theorems about the compiled machine code of sha3 0.12.0. Each theorem is about one call to a
wrapper around `Digest::digest`, or around the sequence `Digest::new`, `update`, `finalize`, for one
of the eight hashers `Sha3_224`, `Sha3_256`, `Sha3_384`, `Sha3_512`, `Keccak224`, `Keccak256`,
`Keccak384` and `Keccak512`. It says that a well-formed call writes exactly the digest that the
hasher's specification computes. The theorems are in [`Statements.lean`](Statements.lean); for
SHA-3 they state the FIPS 202 functions in [`Standards/NIST/SHA3/`](../Standards/NIST/SHA3/)
directly, and for Keccak the specifications in [`Spec/Keccak.lean`](Spec/Keccak.lean), built on the
same FIPS 202 functions.

## Verified operations

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| [`Sha3_224`](https://docs.rs/sha3/0.12.0/sha3/struct.Sha3_224.html): [`digest`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.digest); [`new`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.new), [`update`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.update), [`finalize`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.finalize) | `sha3_224_digest_writes_sha3_224_of_data`; `sha3_224_digest_slices_writes_sha3_224_of_message` | `SHA3.SHA3_224` | [FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf) §6.1 |
| [`Sha3_256`](https://docs.rs/sha3/0.12.0/sha3/struct.Sha3_256.html): [`digest`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.digest); [`new`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.new), [`update`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.update), [`finalize`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.finalize) | `sha3_256_digest_writes_sha3_256_of_data`; `sha3_256_digest_slices_writes_sha3_256_of_message` | `SHA3.SHA3_256` | [FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf) §6.1 |
| [`Sha3_384`](https://docs.rs/sha3/0.12.0/sha3/struct.Sha3_384.html): [`digest`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.digest); [`new`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.new), [`update`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.update), [`finalize`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.finalize) | `sha3_384_digest_writes_sha3_384_of_data`; `sha3_384_digest_slices_writes_sha3_384_of_message` | `SHA3.SHA3_384` | [FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf) §6.1 |
| [`Sha3_512`](https://docs.rs/sha3/0.12.0/sha3/struct.Sha3_512.html): [`digest`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.digest); [`new`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.new), [`update`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.update), [`finalize`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.finalize) | `sha3_512_digest_writes_sha3_512_of_data`; `sha3_512_digest_slices_writes_sha3_512_of_message` | `SHA3.SHA3_512` | [FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf) §6.1 |
| [`Keccak224`](https://docs.rs/sha3/0.12.0/sha3/struct.Keccak224.html): [`digest`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.digest); [`new`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.new), [`update`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.update), [`finalize`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.finalize) | `keccak224_digest_writes_keccak224_of_data`; `keccak224_digest_slices_writes_keccak224_of_message` | `Keccak.keccak224` | [Keccak submission v3](https://keccak.team/files/Keccak-submission-3.pdf) §2 |
| [`Keccak256`](https://docs.rs/sha3/0.12.0/sha3/struct.Keccak256.html): [`digest`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.digest); [`new`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.new), [`update`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.update), [`finalize`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.finalize) | `keccak256_digest_writes_keccak256_of_data`; `keccak256_digest_slices_writes_keccak256_of_message` | `Keccak.keccak256` | [Keccak submission v3](https://keccak.team/files/Keccak-submission-3.pdf) §2 |
| [`Keccak384`](https://docs.rs/sha3/0.12.0/sha3/struct.Keccak384.html): [`digest`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.digest); [`new`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.new), [`update`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.update), [`finalize`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.finalize) | `keccak384_digest_writes_keccak384_of_data`; `keccak384_digest_slices_writes_keccak384_of_message` | `Keccak.keccak384` | [Keccak submission v3](https://keccak.team/files/Keccak-submission-3.pdf) §2 |
| [`Keccak512`](https://docs.rs/sha3/0.12.0/sha3/struct.Keccak512.html): [`digest`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.digest); [`new`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.new), [`update`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.update), [`finalize`](https://docs.rs/digest/0.11.3/digest/trait.Digest.html#tymethod.finalize) | `keccak512_digest_writes_keccak512_of_data`; `keccak512_digest_slices_writes_keccak512_of_message` | `Keccak.keccak512` | [Keccak submission v3](https://keccak.team/files/Keccak-submission-3.pdf) §2 |

The methods are [digest 0.11.3](https://docs.rs/crate/digest/0.11.3/source/src/digest.rs)'s
`Digest::digest` (`src/digest.rs:126-130`), `Digest::new` (`61-63`), `Digest::update` (`76-78`) and
`Digest::finalize` (`87-89`). `Default` of the hashers, which `Digest::digest` and `Digest::new`
call, is covered by every theorem.

## Theorem statements

Each theorem states that if the hypotheses below hold, the conclusion below holds. In Lean, the
hypotheses are the theorem's arguments `hCall`, `hMachine` and `hBindings`, and the conclusion is
the statement after the colon. `hCall` is `ValidDigestCall` in the `digest` theorems and
`ValidCall` in the `new`, `update`, `finalize` theorems.

### Theorem Conclusions

- **The call returns, with one result.** Every successful run from the same starting state ends in
  the same final state (`UniqueExecution`).
- **The output is the specification's digest.** No call can fail, so there is no status. The
  output buffer, read from final memory (`readDigestOutput`, `readOutput`), holds the
  specification's digest of the message. That is the hasher's specification, such as
  `SHA3.SHA3_256`, applied to the message's bits, each byte read least significant bit first
  (`SHA3.bytesToBits`). The resulting bits are packed into bytes, eight at a time, least
  significant bit first (`SHA3.Digest.ofBits`). For `new`, `update`, `finalize`, the message is the
  slices' bytes joined in order (`message`).
- **The call writes nothing else.** Memory changes only in the output buffer and the stack
  (`MemoryWriteFrame`).
- **The caller's state is intact.** RBX, RBP and R12 to R15 (`CalleeSavedRegistersUnchanged`) and
  the clear direction flag (`DirectionFlagUnset`) are preserved, and the machine is again in a
  supported state (`SupportedIntegerMachineState`, `MachineRamUnitStrideDecodable`).

### Theorem Hypotheses

Every theorem has three hypotheses:

- **`hCall`: the call is well formed**, with its arguments passed as the [calling
  convention](#calling-convention) describes. The docstrings of both predicates in
  [`Spec/Program.lean`](Spec/Program.lean) list every condition; in short:
  - one-shot digest: the message is in memory at RDI, and RSI is its length;
  - digest of slices: RSI is the slice count, the tables at RDI and RDX hold the slices' addresses
    and lengths, and every slice is in memory at its address;
  - the output buffer, of the hasher's digest size, is in RAM;
  - every pointer is nonzero, even when the region it points to is empty, including each slice's
    address in a table: Rust's rule for `core::slice::from_raw_parts` and references, which the
    wrappers use;
  - the stack has room for the call: the `minStackBytes` bytes below RSP and the 8-byte return
    slot at RSP are in RAM, and RSP is 8 more than a multiple of 16;
  - the output and the stack are disjoint from each other and from every region the call only
    reads, and avoid the program and the page tables; the regions the call only reads may overlap
    one another and the program;
  - every region ends strictly below 4 GiB (`userAddressLimit`);
  - the message, the tables, the slices and the output need not be aligned, although Rust's
    `core::slice::from_raw_parts`, which the wrappers apply to the tables, requires them to be
    eight-byte aligned;
  - the program is loaded at its link-time addresses, RIP is at the entry point, the direction flag
    is clear, and the return address in the slot at RSP is below 4 GiB and outside the program.
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
    `rep movs` and `rep stos`);
  - the processor reports whether it supports the leading-zero-count instruction (LZCNT), which
    the instruction decoder needs to know.

### Calling convention

The theorems are about machine code, so they reference registers and memory, not Rust values. Each
verified function is reached through a small wrapper in [`program/src/lib.rs`](program/src/lib.rs),
such as `sha3_256_digest` for `Sha3_256::digest`. A wrapper is an exported function that turns its
pointer and length arguments into byte slices, hashes them with a new hasher on each call, and
writes the digest to the output buffer. A wrapper's name starts with its hasher's prefix:
`sha3_224`, `sha3_256`, `sha3_384`, `sha3_512`, `keccak224`, `keccak256`, `keccak384` or
`keccak512`. Calls follow System V, the standard x86-64 convention. The wrappers with a theorem
take their arguments in one of two shapes:

- **one-shot digest** (`<prefix>_digest`) hashes a message passed as one slice;
- **digest of slices** (`<prefix>_digest_slices`) hashes a message passed as several slices.

In both shapes, the output buffer receives the digest: 28 bytes for `Sha3_224` and `Keccak224`, 32
for `Sha3_256` and `Keccak256`, 48 for `Sha3_384` and `Keccak384`, and 64 for `Sha3_512` and
`Keccak512` (each `Routine`'s `outputBytes` in [`Spec/Program.lean`](Spec/Program.lean)).

#### One-shot digest

`<prefix>_digest` hashes the message with `Digest::digest`:

| Argument | Register | Holds |
| --- | --- | --- |
| `data` | RDI | address of the message |
| `len` | RSI | length of the message in bytes |
| `out` | RDX | address of the output buffer, of the hasher's digest size |
| return value | none | none: the call cannot fail |

#### Digest of slices

`<prefix>_digest_slices` takes the message as `num_inputs` slices, slice `i` being the
`input_lens[i]` bytes at `input[i]`. It hashes them with `Digest::new`, `update` once per slice in
order, and `finalize`:

| Argument | Register | Holds |
| --- | --- | --- |
| `input` | RDI | address of a table of the slices' addresses, eight bytes each |
| `num_inputs` | RSI | number of slices |
| `input_lens` | RDX | address of a table of the slices' lengths, eight bytes each |
| `out` | RCX | address of the output buffer, of the hasher's digest size |
| return value | none | none: the call cannot fail |

## Building the verified binary

The theorems are about the machine code checked in under
[`Spec/Program/Extracted/`](Spec/Program/Extracted/) (`text.bin` and `rodata.bin`). It is built
from the wrapper crate in [`program/`](program/):

```sh
cd Sha3/program
cargo build --locked --release   # target/x86_64-unknown-none/release/libsha3_program.a
```

[`scripts/extract.py`](../scripts/extract.py) runs this build with `--remap-path-prefix` flags, so
that the bytes do not depend on where the repository is checked out. It then links the library into
a fixed image with the shared [`scripts/layout.ld`](../scripts/layout.ld) and extracts `.text` and
`.rodata` with lean-x86's `x86-extract`. To reproduce the verified bytes, run from the repository
root:

```sh
bash ci/check-extraction.sh Sha3   # rebuild, extract and compare with the checked-in files
python3 scripts/extract.py Sha3    # rebuild and regenerate Spec/Program/Extracted/
```

This requires the following settings:

| Setting | Value |
| --- | --- |
| Compiler | Rust 1.98.1 (`program/rust-toolchain.toml`) |
| Target | `x86_64-unknown-none` at x86-64-v1 (`program/.cargo/config.toml`) |
| Layout | `scripts/layout.ld`: code at 0x100000, read-only data at 0x200000 |
| Features on | `oid` |
| Features off | `alloc`, `zeroize` |
| Keccak permutation | keccak's portable `u64` permutation (`--cfg keccak_backend="soft"`) |
