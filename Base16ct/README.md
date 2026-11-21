# base16ct 1.0.0

Theorems about the compiled machine code of
[base16ct 1.0.0](https://docs.rs/base16ct/1.0.0/base16ct/), the hex (RFC 4648 base 16) encoders
and decoders. Each theorem is about one call to a wrapper around one of the crate's functions, and
says that a well-formed call does exactly what the specification of that function in
[`Spec/Base16.lean`](Spec/Base16.lean) computes. The theorems are in
[`Statements.lean`](Statements.lean); the specification is built on RFC 4648 in
[`Standards/RFC/BaseEncodings/`](../Standards/RFC/BaseEncodings/).

## Verified operations

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| [`lower::encode`](https://docs.rs/base16ct/1.0.0/base16ct/lower/fn.encode.html) | `base16ct_lower_encode_writes_lowercase_hex_or_rejects_short_buffer` | `Base16.lowerEncoder` | [RFC 4648 §8](https://www.rfc-editor.org/rfc/rfc4648#section-8) |
| [`lower::encode_str`](https://docs.rs/base16ct/1.0.0/base16ct/lower/fn.encode_str.html) | `base16ct_lower_encode_str_writes_lowercase_hex_or_rejects_short_buffer` | `Base16.lowerEncoder` | [RFC 4648 §8](https://www.rfc-editor.org/rfc/rfc4648#section-8) |
| [`upper::encode`](https://docs.rs/base16ct/1.0.0/base16ct/upper/fn.encode.html) | `base16ct_upper_encode_writes_uppercase_hex_or_rejects_short_buffer` | `Base16.upperEncoder` | [RFC 4648 §8](https://www.rfc-editor.org/rfc/rfc4648#section-8) |
| [`upper::encode_str`](https://docs.rs/base16ct/1.0.0/base16ct/upper/fn.encode_str.html) | `base16ct_upper_encode_str_writes_uppercase_hex_or_rejects_short_buffer` | `Base16.upperEncoder` | [RFC 4648 §8](https://www.rfc-editor.org/rfc/rfc4648#section-8) |
| [`lower::decode`](https://docs.rs/base16ct/1.0.0/base16ct/lower/fn.decode.html) | `base16ct_lower_decode_writes_decoded_bytes_or_rejects` | `Base16.decodeInto Base16.lowerDecoder` | [RFC 4648 §8](https://www.rfc-editor.org/rfc/rfc4648#section-8) |
| [`upper::decode`](https://docs.rs/base16ct/1.0.0/base16ct/upper/fn.decode.html) | `base16ct_upper_decode_writes_decoded_bytes_or_rejects` | `Base16.decodeInto Base16.upperDecoder` | [RFC 4648 §8](https://www.rfc-editor.org/rfc/rfc4648#section-8) |
| [`mixed::decode`](https://docs.rs/base16ct/1.0.0/base16ct/mixed/fn.decode.html) | `base16ct_mixed_decode_writes_decoded_bytes_or_rejects` | `Base16.decodeInto Base16.mixedDecoder` | [RFC 4648 §8](https://www.rfc-editor.org/rfc/rfc4648#section-8), letters in either case |
| [`decoded_len`](https://docs.rs/base16ct/1.0.0/base16ct/fn.decoded_len.html) | `base16ct_decoded_len_writes_half_length_or_rejects_odd_length` | `Base16.decodedLength` | [RFC 4648 §8](https://www.rfc-editor.org/rfc/rfc4648#section-8) |
| [`encoded_len`](https://docs.rs/base16ct/1.0.0/base16ct/fn.encoded_len.html) | `base16ct_encoded_len_writes_twice_length` | `2 * byteLength` | [RFC 4648 §8](https://www.rfc-editor.org/rfc/rfc4648#section-8) |

## Theorem statements

Each theorem states that if the hypotheses below hold, the conclusion below holds. In Lean, the
hypotheses are the theorem's arguments `hCall`, `hMachine` and `hBindings`, and the conclusion is
the statement after the colon. The theorems about `encode`, `encode_str` and `decode` use the call
predicate `ValidCall`, and those about `decoded_len` and `encoded_len` use `ValidLengthCall`.

### Theorem Conclusions

- **The call returns, with one result.** Every successful run from the same starting state ends in
  the same final state (`UniqueExecution`).
- **The result is the specification's.** EAX is 0 (`SuccessfulStatus`) or the error's status
  (`FailureStatus`, with `invalidLengthStatus` or `invalidEncodingStatus`), as the specification
  decides; `encoded_len` has no status. On success, the output bytes (`readOutput`) and the length
  word (`readLengthOutput`) hold the specification's result; both are read from final memory at
  the initial pointers. The two length theorems read only the length word.
- **The call writes nothing else.** On success, memory changes only in the output bytes written,
  the length word and the stack region. On `InvalidLength`, it changes only in the stack region. On
  `InvalidEncoding`, it changes only in the stack region and the first `input.size / 2` output
  bytes, whose new values the theorems leave unstated (`MemoryWriteFrame`).
- **The caller's state is intact.** RBX, RBP and R12 to R15 (`CalleeSavedRegistersUnchanged`) and
  the clear direction flag (`DirectionFlagUnset`) are preserved, and the machine is again in a
  supported state.

### Theorem Hypotheses

Every theorem has three hypotheses:

- **`hCall`: the call is well formed** (`ValidCall routine initial input outputCapacity …` or
  `ValidLengthCall routine initial byteLength …`), with its arguments passed as the [calling
  convention](#calling-convention) describes. The docstrings of `ValidCall` and `ValidLengthCall` in
  [`Spec/Program.lean`](Spec/Program.lean) list every condition; in short:
  - RIP at the wrapper's entry, the program loaded at its link-time addresses, the direction flag
    clear;
  - the input at RDI, non-null even when empty, with its length in RSI; the length calls read none
    of its bytes but still need them allocated, as the `&[u8]` the wrapper builds requires;
  - for `ValidCall`, the whole `dst_len`-byte output buffer at RCX non-null and allocated on every
    call, rejected ones included, as the `&mut [u8]` the wrapper builds requires; `dst_len` in R8;
  - the 8-byte length word at RDX allocated, required only when the call writes it; its address
    need not be non-null or aligned, as the wrappers write through the raw pointer;
  - every region ending strictly below 4 GiB (`userAddressLimit`), so a region ending at 2^32 is
    not covered;
  - the stack budget, `minStackBytes` bytes below RSP, and the 8-byte return slot at RSP allocated,
    with RSP 8 more than a multiple of 16;
  - the return address below 4 GiB and outside the program;
  - for `ValidCall`, the input, the output buffer and the stack region pairwise disjoint; the
    length word disjoint from the output bytes the call writes and from the stack region, but free
    to overlap the input and the rest of the output buffer;
  - for `ValidLengthCall`, the input free to overlap the stack region and the length word, and the
    length word, when written, disjoint from the stack region;
  - everything the call writes clear of the program and the page tables.
- **`hMachine`: the processor is in a supported state** (`SupportedIntegerMachineState`); in short:
  - 64-bit mode, with supported control-register settings and SSE enabled;
  - page tables at 0x1000 map the first 4 GiB to the same addresses (identity mapping);
  - the processor is ready to start an instruction: no interrupt or other event is pending and no
    debug trap is detected.
- **`hBindings`: memory and string instructions behave normally**
  (`MachineRamUnitStrideDecodable`):
  - no address is in the range reserved for system-management mode (SMRR), and memory below 4 GiB
    has the normal cached memory type (write-back);
  - string instructions step one element at a time (the compiled code uses no string
    instruction);
  - the processor reports whether it supports the leading-zero-count instruction (LZCNT), which
    the instruction decoder needs to know.

### Calling convention

The theorems are about machine code, so they reference registers and memory, not Rust values. Each
verified function is reached through a small wrapper in [`program/src/lib.rs`](program/src/lib.rs),
such as `base16ct_lower_encode` for `lower::encode`. Each of the 9 wrappers is an exported
`extern "C"` function that builds Rust slices from its pointer arguments, calls one base16ct
function, and stores the length of the result. Calls follow System V, the standard x86-64
convention. The arguments come in one order, `src, src_len, out_len, dst, dst_len`, and each
wrapper takes the ones it needs. There are two kinds of wrapper, one per subsection below.

#### Encode and decode wrappers

The seven wrappers of `encode`, `encode_str` and `decode` (`base16ct_lower_encode`,
`base16ct_upper_encode`, `base16ct_lower_encode_str`, `base16ct_upper_encode_str`,
`base16ct_lower_decode`, `base16ct_upper_decode`, `base16ct_mixed_decode`) take all five arguments
and write the result to an output buffer (`ValidCall`):

| Argument | Register | Holds |
| --- | --- | --- |
| `src` | RDI | address of the input bytes |
| `src_len` | RSI | number of input bytes |
| `out_len` | RDX | address of an 8-byte word that receives the length of the result, which the wrapper stores only on success |
| `dst` | RCX | address of the output buffer |
| `dst_len` | R8 | size of the output buffer, its capacity |
| return value | EAX | 32-bit status: 0 on success, 1 (`invalidLengthStatus`) for `Error::InvalidLength`, 2 (`invalidEncodingStatus`) for `Error::InvalidEncoding` |

On success, the result fills the start of the output buffer: `2 * src_len` bytes from an encoder
and `src_len / 2` from a decoder. The length word holds their number, eight bytes little-endian.

#### Length wrappers

`base16ct_decoded_len` and `base16ct_encoded_len` take the first three arguments
(`ValidLengthCall`) and read only the length of `src`:

| Argument | Register | Holds |
| --- | --- | --- |
| `src` | RDI | address of the input bytes, none of which the call reads |
| `src_len` | RSI | number of input bytes |
| `out_len` | RDX | address of an 8-byte word that receives the computed length; `base16ct_decoded_len` stores it only on success |
| return value | EAX | for `base16ct_decoded_len`, a 32-bit status: 0 on success, 1 (`invalidLengthStatus`) for an odd `src_len`; `base16ct_encoded_len` returns no status |

## Deliberate differences from the standards

The specification records an intentional deviation of RustCrypto from a standard in one operation.

- **Hex letters in either case**
  - *Specification:* `mixed::decode` accepts `a`–`f` and `A`–`F`, mixed within one input
    (`Base16.mixedDecoder`).
  - *Standard:* RFC 4648 §3.3 says implementations "MUST reject the encoded data if it contains
    characters outside the base alphabet", and Table 5 has only `A`–`F`.
  - *Why:* base16ct documents this: its `mixed` module provides the case-insensitive decoding
    ("Function for decoding mixed Base16 (hex)", `base16ct-1.0.0/src/lib.rs`), and RFC 4648 §8 calls
    base 16 "the standard case-insensitive hex encoding". `Base16.mixedDecoder` uses
    `decodeIgnoringCase`, which documents this departure.

## Building the verified binary

The theorems are about the machine code checked in under
[`Spec/Program/Extracted/`](Spec/Program/Extracted/) (`text.bin`). It is built from the wrapper
crate in [`program/`](program/):

```sh
cd Base16ct/program
cargo build --locked --release   # target/x86_64-unknown-none/release/libbase16ct_program.a
```

[`scripts/extract.py`](../scripts/extract.py) runs this build with `--remap-path-prefix` flags, so
that the bytes do not depend on where the repository is checked out. It then links the library into
a fixed image with the shared [`scripts/layout.ld`](../scripts/layout.ld) and extracts `.text` with
lean-x86's `x86-extract`. To reproduce the verified bytes, run from the repository root:

```sh
bash ci/check-extraction.sh Base16ct   # rebuild, extract and compare with the checked-in files
python3 scripts/extract.py Base16ct    # rebuild and regenerate Spec/Program/Extracted/
```

This requires the following settings:

| Setting | Value |
| --- | --- |
| Compiler | Rust 1.98.1 (`program/rust-toolchain.toml`) |
| Target | `x86_64-unknown-none` at x86-64-v1 (`program/.cargo/config.toml`) |
| Layout | [`scripts/layout.ld`](../scripts/layout.ld), the shared fixed layout: code at 0x100000 and read-only data at 0x200000; no writable static data |
| Features on | none (`default-features = false`) |
| Features off | `alloc` |
