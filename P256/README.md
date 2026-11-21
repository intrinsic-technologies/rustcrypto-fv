# p256 0.14.0

Theorems about the compiled machine code of p256 0.14.0. Each theorem is about one call to a
wrapper around one of the crate's functions, and says that a well-formed call does exactly what the
specification of that function in [`Spec/`](Spec/) computes. The theorems are in
[`Statements.lean`](Statements.lean); the specifications are built on the standards in
[`Standards/`](../Standards/README.md).

## Verified operations

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| [`PublicKey::from_sec1_bytes`](https://docs.rs/crate/elliptic-curve/0.14.3/source/src/public_key.rs#126) | `p256_public_key_from_sec1_bytes_writes_public_key_or_rejects_encoding` | `Keys.publicKeyFromSec1` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §2.3.3–§2.3.4 |
| [`Signer::try_sign`](https://docs.rs/crate/ecdsa/0.17.0/source/src/signing.rs#185) for [`SigningKey`](https://docs.rs/ecdsa/0.17.0/ecdsa/struct.SigningKey.html) | `p256_signing_key_try_sign_writes_signature_or_never_returns` | `Ecdsa.signMessage` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §4.1.3; [RFC 6979 §3.2](https://www.rfc-editor.org/rfc/rfc6979#section-3.2); [FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf) (SHA-256) |
| [`Verifier::verify`](https://docs.rs/crate/ecdsa/0.17.0/source/src/verifying.rs#170) for [`VerifyingKey`](https://docs.rs/ecdsa/0.17.0/ecdsa/struct.VerifyingKey.html) | `p256_verifying_key_verify_accepts_signature_or_rejects_signature` | `Ecdsa.verifyMessage` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §4.1.4; [FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf) (SHA-256) |
| [`Signature::from_slice`](https://docs.rs/crate/ecdsa/0.17.0/source/src/lib.rs#212) | `p256_signature_from_slice_writes_signature_or_rejects_bytes` | `Ecdsa.signatureFromSlice` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §2.3.8, §4.1.4 |
| [`Generate::generate_from_rng`](https://docs.rs/crate/crypto-common/0.2.2/source/src/generate.rs#17) for [`SigningKey`](https://docs.rs/ecdsa/0.17.0/ecdsa/struct.SigningKey.html) | `p256_signing_key_generate_from_rng_writes_signing_key` | `Generate.generatedSigningKey` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §3.2.1 |
| [`ecdh::diffie_hellman`](https://docs.rs/crate/elliptic-curve/0.14.3/source/src/ecdh.rs#61) | `p256_ecdh_diffie_hellman_writes_shared_secret` | `Ecdh.diffieHellman` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §3.3.1 |

The specifications take the curve's constants and its field and scalar arithmetic from
[SP 800-186 §3.2.1.3](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-186.pdf)
(`Standards/NIST/EllipticCurves/`), and its points and group law from
[SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §2.2.1 (`Standards/SECG/ECC/`).

## Theorem statements

Each theorem states that if the hypotheses below hold, the conclusion below holds. In Lean, the
hypotheses are the theorem's arguments `hCall`, `hMachine` and `hBindings`, and the conclusion is
the statement after the colon.

### Theorem Conclusions

- **The call returns, with one result.** Every successful run from the same starting state ends in
  the same final state (`UniqueExecution`). The one exception is `try_sign`: when no RFC 6979 nonce
  candidate gives a signature (`Ecdsa.NeverSigns`), it never returns (`NeverReturns`).
- **The result is the specification's.** For a function that can fail, EAX is 0
  (`SuccessfulStatus`) when the specification gives a result, and the function's failure status
  (`FailureStatus`) when it gives `none`. A function that cannot fail has no status. On success the
  output holds the specification's result (`readOutput`); on failure the output is untouched.
- **The call writes nothing else.** Memory changes only in the output (on success), the
  allocator's state, the random source and the stack (`MemoryWriteFrame`).
- **The caller's state is intact.** RBX, RBP and R12 to R15 (`CalleeSavedRegistersUnchanged`) and
  the clear direction flag (`DirectionFlagUnset`) are preserved, and the machine is again in a
  supported state (`SupportedIntegerMachineState`, `MachineRamUnitStrideDecodable`).

### Theorem Hypotheses

Every theorem has three hypotheses:

- **`hCall`: the call is well formed** (`ValidCall routine initial inputs`), with its arguments
  passed as the [calling convention](#calling-convention) describes. The docstrings of `ValidCall`
  and `ValidCallWithSlices` in [`Spec/Program.lean`](Spec/Program.lean) list every condition; in
  short:
  - the program loaded at its link-time addresses, RIP at the entry, the direction flag clear;
  - the slices hold valid values of the function's Rust arguments; for `generate_from_rng`, random
    bytes that hold a 32-byte block in `[1, n − 1]`;
  - the output buffer is large enough for the result;
  - the stack has room for the call (`routine.minStackBytes`, in `Spec/Program/Functions.lean`);
  - the regions the call writes (heap, statics, stack and, on success, the output) are disjoint
    from one another and from everything the call reads;
  - every region lies below 4 GiB (`userAddressLimit`);
  - the theorems do not require the address and length tables to be aligned, although the
    wrapper's `slice::from_raw_parts` does;
  - a return address below `userAddressLimit`, outside the program.
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
verified function is reached through a small wrapper in `program/src/` (`keys.rs`, `signatures.rs`,
`extras.rs`), such as `p256_signing_key_try_sign` for `Signer::try_sign`. A wrapper is an exported
function that decodes byte slices into the Rust function's arguments, calls the function, and
writes the result to a buffer. Calls follow System V, the standard x86-64 convention, and every
P256 wrapper takes the same arguments (`program/src/abi.rs`):

| Argument | Register | Holds |
| --- | --- | --- |
| `input` | RDI | address of a table of addresses, one per byte slice |
| `num_inputs` | RSI | number of slices |
| `input_lens` | RDX | address of a table of the slices' lengths |
| `output` | RCX | address of the output buffer |
| `capacity` | R8 | size of the output buffer |
| `heap` | R9 | address of a scratch heap; no function with a theorem uses it |
| `heap_len` | first stack argument | size of the heap |
| return value | EAX | 0 on success, 1 for the crate's error (`invalidPublicKeyStatus` and the others in `Spec/Program.lean`) |

On success the output buffer holds the result's length, eight bytes little-endian, then the
result's bytes. The wrappers also use 40 bytes of statics at 0x300000: the allocator's state
(`allocatorStateRegion`) and the random source (`randomSourceRegion`). Every wrapper empties the
random source on entry. `SigningKey::generate_from_rng` reads the caller's random bytes from one
slice, in order.

## Deliberate differences from the standards

The specification records intentional deviations of RustCrypto from a standard in two
operations.

- **Compact points `05 ‖ x`**
  - *Specification:* `PublicKey::from_sec1_bytes` accepts RustCrypto's compact form, the 33 bytes
    `05 ‖ x`, as the point with that `x` and the smaller of its two possible `y` values
    (`Points.decompact`). The point argument of `ecdh::diffie_hellman`, which the wrapper decodes
    the same way, may be in this form too (`Points.isAffineEncoding`).
  - *Standard:* SEC 1 v2.0 §2.3.4 step 2.3 outputs "invalid" for a 33-octet string whose first octet
    is not `02` or `03`, and RFC 5480 §2.2 says "The public key MUST be rejected if any other value
    is included in the first octet."
  - *Why:* the compiled crate accepts this form, and the specification states what it does. The
    documentation of `from_sec1_bytes` describes only SEC 1 (elliptic-curve 0.14.3
    `src/public_key.rs:115-124`), but that is an error in the docs: the rest of the crate assumes
    the compact form, which sec1 0.8.1 names in its public API (`Tag::Compact`,
    `src/point.rs:521-522`) and primeorder's point decoder handles (`DecompactPoint::decompact`).
- **ECDH with the identity**
  - *Specification:* with the identity as `public_key`, the shared secret is 32 zero bytes, the `x`
    p256 stores for the identity (`Ecdh.sharedX`).
  - *Standard:* SEC 1 v2.0 §3.3.1 outputs "invalid" when the product is the point at infinity, which
    for a secret in `[1, n − 1]` happens only for the identity.
  - *Why:* the compiled crate returns these bytes, and the specification states what it does. The
    documentation of `ecdh::diffie_hellman` claims no standard and does not describe the identity
    case, though its signature admits it: it takes any `AffinePoint` and returns a `SharedSecret`
    with no error (elliptic-curve 0.14.3 `src/ecdh.rs:41-71`).

## Building the verified binary

The theorems are about the machine code checked in under
[`Spec/Program/Extracted/`](Spec/Program/Extracted/) (`text.bin` and `rodata.bin`). It is built from
the wrapper crate in [`program/`](program/):

```sh
cd P256/program
cargo build --locked --release   # target/x86_64-unknown-none/release/libp256_program.a
```

[`scripts/extract.py`](../scripts/extract.py) runs this build with `--remap-path-prefix` flags, so
that the bytes do not depend on where the repository is checked out. It then links the library into
a fixed image with `program/layout.ld` and extracts `.text` and `.rodata` with lean-x86's
`x86-extract`. To reproduce the verified bytes, run from the repository root:

```sh
bash ci/check-extraction.sh P256   # rebuild, extract and compare with the checked-in files
python3 scripts/extract.py P256    # rebuild and regenerate Spec/Program/Extracted/
```

This requires the following settings:

| Setting | Value |
| --- | --- |
| Compiler | Rust 1.98.1 (`program/rust-toolchain.toml`) |
| Target | `x86_64-unknown-none` at x86-64-v1 (`program/.cargo/config.toml`) |
| Layout | `program/layout.ld`: fixed addresses, with `.bss` at 0x300000 |
| Features on | `alloc`, `arithmetic`, `ecdh`, `ecdsa` (`sha256`, `digest`), `getrandom`, `group-digest`, `hash2curve`, `oprf`, `pem`, `pkcs8`, `serde` |
| Features off | `std`; `precomputed-tables` |
| SHA-256 | sha2's software backend (`--cfg sha2_backend="soft"`) |
| Randomness | getrandom's custom backend (`--cfg getrandom_backend="custom"`) |
