# k256 0.14.0

Theorems about the compiled machine code of RustCrypto's
[`k256`](https://docs.rs/k256/0.14.0/k256/) 0.14.0, the secp256k1 curve. Each theorem is about one
call to a wrapper around one of the crate's functions, and says that a well-formed call does
exactly what the specification of that function in [`Spec/`](Spec/) computes. The theorems are in
[`Statements.lean`](Statements.lean); the specifications are built on the standards in
[`Standards/`](../Standards/README.md).

## Verified operations

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| [`Signer::try_sign`](https://docs.rs/crate/ecdsa/0.17.0/source/src/signing.rs#185) for [`SigningKey`](https://docs.rs/ecdsa/0.17.0/ecdsa/struct.SigningKey.html) | `k256_signing_key_try_sign_writes_low_s_signature_or_never_returns` | `Ecdsa.signature` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §4.1.3, [RFC 6979 §3.2](https://www.rfc-editor.org/rfc/rfc6979#section-3.2), low `s` ([BIP 62](https://github.com/bitcoin/bips/blob/c0614759ed8c878c7ff45a1d0326e88711bab13e/bip-0062.mediawiki#low-s-values-in-signatures)) |
| [`Verifier::verify`](https://docs.rs/crate/ecdsa/0.17.0/source/src/verifying.rs#170) for [`VerifyingKey`](https://docs.rs/ecdsa/0.17.0/ecdsa/struct.VerifyingKey.html) | `k256_verifying_key_verify_accepts_signature_or_rejects_signature` | `Ecdsa.verifies` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §4.1.4, low `s` ([BIP 62](https://github.com/bitcoin/bips/blob/c0614759ed8c878c7ff45a1d0326e88711bab13e/bip-0062.mediawiki#low-s-values-in-signatures)) |
| [`Signature::from_slice`](https://docs.rs/crate/ecdsa/0.17.0/source/src/lib.rs#212) | `k256_signature_from_slice_writes_signature_or_rejects_bytes` | `Ecdsa.signatureScalars`, `Ecdsa.signatureBytes` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §§2.3.7–2.3.8, §4.1.4 step 1 |
| [`Generate::generate_from_rng`](https://docs.rs/crate/crypto-common/0.2.2/source/src/generate.rs#17) for [`SigningKey`](https://docs.rs/ecdsa/0.17.0/ecdsa/struct.SigningKey.html) | `k256_signing_key_generate_from_rng_writes_signing_key` | `Secp256k1.generatedSigningKey` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §3.2.1 |
| [`PublicKey::from_sec1_bytes`](https://docs.rs/crate/elliptic-curve/0.14.3/source/src/public_key.rs#126) | `k256_public_key_from_sec1_bytes_writes_public_key_or_rejects_encoding` | `Secp256k1.decodePublicKey` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §2.3.4 |
| [`ecdh::diffie_hellman`](https://docs.rs/crate/elliptic-curve/0.14.3/source/src/ecdh.rs#61) | `k256_ecdh_diffie_hellman_writes_shared_secret` | `Secp256k1.sharedSecret` | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §3.3.1 |

The specifications take the secp256k1 parameters from
[SEC 2 v2.0](https://www.secg.org/sec2-v2.pdf) §2.4.1
(`Standards/SECG/DomainParameters/Secp256k1.lean`), and the curve, its group law and point
encodings from [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf) §2 (`Standards/SECG/ECC/`). Point
decompression takes square roots modulo `p` from
[SP 800-186](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-186.pdf)
Appendix E.3 (`Standards/NIST/EllipticCurves/Field.lean`).

## Theorem statements

Each theorem states that if the hypotheses below hold, the conclusion below holds. In Lean, the
hypotheses are the theorem's arguments `hCall`, `hMachine` and `hBindings`, and the conclusion is
the statement after the colon.

### Theorem Conclusions

- **The call returns, with one result.** Every successful run from the same starting state ends in
  the same final state (`UniqueExecution`). The one exception is `try_sign`: when RFC 6979's nonce
  search never succeeds (`Ecdsa.NonceSearchSucceeds` is false), it never returns (`NeverReturns`).
- **The result is the specification's.** For a function that can fail, EAX is 0
  (`SuccessfulStatus`) when the specification accepts, and the function's failure status
  (`FailureStatus`) when it rejects. A function that cannot fail has no status. On success the
  output holds the specification's result (`readOutput`); on failure the output is untouched. The
  verifier writes no output, only its status.
- **The call writes nothing else.** Memory changes only in the output (for a function that can
  fail, only on success) and the stack: the `minStackBytes` bytes below RSP and the 8-byte return
  address slot at RSP (`MemoryWriteFrame`). `MemoryWriteFrame` bounds the final memory only, not
  the writes made during the call.
- **The caller's state is intact.** RBX, RBP and R12 to R15 (`CalleeSavedRegistersUnchanged`) and
  the clear direction flag (`DirectionFlagUnset`) are preserved, and the machine is again in a
  supported state (`SupportedIntegerMachineState`, `MachineRamUnitStrideDecodable`).

### Theorem Hypotheses

Every theorem has three hypotheses:

- **`hCall`: the call is well formed** (`ValidCall routine initial inputs`), with its arguments
  passed as the [calling convention](#calling-convention) describes. The docstring of `ValidCall` in
  [`Spec/Program.lean`](Spec/Program.lean) lists every condition; in short:
  - the program is loaded at its link-time addresses, RIP is at the entry point, and the direction
    flag is clear;
  - each input's address, and a slice's length, are in the registers the calling convention gives;
  - each input is in memory at a nonzero address, even when empty (Rust requires a non-null
    pointer even for an empty slice);
  - each input holds a value of its Rust argument's type, which the wrapper does not check; for
    `generate_from_rng`, random bytes that hold a 32-byte block in `[1, n − 1]`;
  - for a routine that writes an output, the output buffer, `outputBytes` bytes at RDI, is RAM at a
    nonzero address;
  - the stack has room for the call: `minStackBytes` bytes of RAM below RSP and the 8-byte return
    address slot at RSP, with RSP 8 more than a multiple of 16;
  - every input, the output and the stack region end strictly below `userAddressLimit` (2^32);
  - the output and the stack region are disjoint from each other and avoid every input, the
    program and the page tables at `[0x1000, 0x3000)`; the inputs may overlap one another;
  - the return address at RSP is below `userAddressLimit` and outside the program.
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
    `rep movsb`, `rep movsq` and `rep stos`);
  - the processor reports whether it supports the leading-zero-count instruction (LZCNT), which
    the instruction decoder needs to know.

### Calling convention

The theorems are about machine code, so they reference registers and memory, not Rust values. Each
verified function is reached through a small wrapper in [`program/src/lib.rs`](program/src/lib.rs),
such as `k256_signature_from_slice` for `Signature::from_slice`. A wrapper is an exported function
that decodes the caller's bytes into the Rust function's arguments, calls the function, and copies
the result out. Calls follow System V, the standard x86-64 convention, with the arguments in RDI,
RSI, RDX and RCX, in order. A wrapper that writes an output takes the output buffer's address
first, in RDI.

A typed argument (a key, a signature, a point or a scalar) is one the wrapper decodes with a crate
decoder before the call, not one the function the theorem is about decodes itself. `hCall` requires
its bytes to be a valid encoding, so the decoder's own failures are outside the theorems.

The six wrappers with a theorem take their arguments in five shapes, one column each in the table
below, headed by the wrappers and their `Routine`s in `Spec/Program.lean`. A cell gives the
argument's name in `lib.rs`, what it holds and, for a typed argument, the crate decoder that builds
it:

| Register | `k256_signing_key_try_sign` (`signingKeyTrySign`) | `k256_verifying_key_verify` (`verifyingKeyVerify`) | `k256_signature_from_slice` (`signatureFromSlice`), `k256_public_key_from_sec1_bytes` (`publicKeyFromSec1Bytes`) | `k256_signing_key_generate_from_rng` (`signingKeyGenerateFromRng`) | `k256_ecdh_diffie_hellman` (`ecdhDiffieHellman`) |
| --- | --- | --- | --- | --- | --- |
| RDI | `signature`: address of the output, 64 bytes | `public_key`: address of the key's 65-byte uncompressed SEC 1 encoding (`VerifyingKey::from_sec1_bytes`) | `signature` / `public_key`: address of the output, 64 / 65 bytes | `signing_key`: address of the output, 97 bytes | `shared`: address of the output, 32 bytes |
| RSI | `secret`: address of the 32-byte secret key (`SigningKey::from_bytes`) | `msg`: address of the message | `bytes`: address of the bytes | `random`: address of the random bytes | `secret`: address of the 32-byte secret key (`NonZeroScalar::from_repr`) |
| RDX | `msg`: address of the message | `msg_len`: its length | `bytes_len`: their length | `random_len`: their length | `public_key`: address of the point's 33-byte `GroupEncoding` (`GroupEncoding::from_bytes`) |
| RCX | `msg_len`: its length | `signature`: address of the 64-byte signature `r ‖ s` (`Signature::from_bytes`) | | | |
| return value, EAX | none | 0 for a valid signature, 1 (`signatureErrorStatus`) for an invalid one | 0 for `Ok`, 1 for an error (`signatureErrorStatus` / `ellipticCurveErrorStatus`) | none | none |

Each error status is named after its Rust error type. The wrappers of `generate_from_rng`,
`diffie_hellman` and `Signer::try_sign` return nothing, so the theorems claim nothing about EAX.
These functions cannot fail: `try_sign`'s `Result` is `Ok` whenever the call returns (ecdsa 0.17.0
`src/signing.rs:155-159`, `171-173`, `185-187`, `195-200`).

On success the output buffer at RDI holds the result's bytes, the `Routine`'s `outputBytes` of them
(the sizes in the table). `SigningKey::generate_from_rng` takes the wrapper's `CallerBytes`, a
generator that serves the caller's random bytes in order. No wrapper with a theorem allocates or
touches the bump allocator `HEAP`.

## Deliberate differences from the standards

The specification records intentional deviations of RustCrypto from a standard in three
operations.

- **Verification rejects a high `s`**
  - *Specification:* `Verifier::verify` refuses an `s` above `n / 2` (`Ecdsa.verifies`).
    `Signer::try_sign` produces only low-`s` signatures: it replaces a high `s` by `n − s`
    (`Ecdsa.normalizeS`), which SEC 1 v2.0 §4.1.3 permits.
  - *Standard:* SEC 1 v2.0 §4.1.4 accepts an `s` above `n / 2`.
  - *Why:* k256 documents this: its README says its ECDSA is "applying low-S normalization (BIP
    0062) as used in consensus-critical applications", and BIP 62 requires `s` in `[1, n / 2]`. The
    crate sets `EcdsaCurve::NORMALIZE_S = true` (`src/ecdsa.rs:104-106`;
    `ecdsa::hazmat::verify_prehashed`, ecdsa 0.17.0 `src/hazmat.rs:142-144`).
- **Compact point `05 ‖ x` (`from_sec1_bytes`, ECDH)**
  - *Specification:* `PublicKey::from_sec1_bytes` and `GroupEncoding::from_bytes` also accept 33
    bytes `05 ‖ x`, the point with x-coordinate `x` and an even y-coordinate
    (`Secp256k1.decodePublicKey`).
  - *Standard:* SEC 1 v2.0 §2.3.4 defines no `05` tag.
  - *Why:* the compiled crate accepts this form, and the specification states what it does. The
    documentation of `from_sec1_bytes` describes only SEC 1, but that is an error in the docs: the
    rest of the crate assumes the compact form, which RustCrypto's `sec1` crate names in its public
    API (`Tag::Compact`) and k256 decodes with BIP 340's even-`y` rule.
- **ECDH with the identity**
  - *Specification:* the peer point of `ecdh::diffie_hellman` may be the identity (33 zero bytes in
    its `GroupEncoding`), and the shared secret is then 32 zero bytes (`Secp256k1.sharedSecret`).
  - *Standard:* SEC 1 v2.0 §3.3.1 takes only a valid public key, which the identity is not
    (§3.2.2.1).
  - *Why:* the compiled crate returns these bytes, and the specification states what it does. The
    documentation of `diffie_hellman` claims no standard and does not describe the identity case,
    though its signature admits it: it takes any `AffinePoint` and cannot fail. `PublicKey`, the
    type the docs point callers to, never holds the identity.

## Building the verified binary

The theorems are about the machine code checked in under
[`Spec/Program/Extracted/`](Spec/Program/Extracted/) (`text.bin` and `rodata.bin`). It is built from
the wrapper crate in [`program/`](program/):

```sh
cd K256/program
cargo build --locked --release   # target/x86_64-unknown-none/release/libk256_program.a
```

[`scripts/extract.py`](../scripts/extract.py) runs this build with `--remap-path-prefix` flags, so
that the bytes do not depend on where the repository is checked out. It then links the library into
a fixed image with `program/layout.ld` and extracts `.text` and `.rodata` with lean-x86's
`x86-extract`. To reproduce the verified bytes, run from the repository root:

```sh
bash ci/check-extraction.sh K256   # rebuild, extract and compare with the checked-in files
python3 scripts/extract.py K256    # rebuild and regenerate Spec/Program/Extracted/
```

This requires the following settings:

| Setting | Value |
| --- | --- |
| Compiler | Rust 1.98.1 (`program/rust-toolchain.toml`) |
| Target | `x86_64-unknown-none` at x86-64-v1 (`program/.cargo/config.toml`) |
| Layout | `program/layout.ld`: fixed addresses, with `.bss` (the wrapper's 16-byte `HEAP`) at 0x300000 and no `.data` |
| Features on | `alloc`, `arithmetic`, `ecdh`, `ecdsa` (`sha256`), `pkcs8`, `schnorr` (`sha256`) |
| Features off | `std`; `precomputed-tables`; `critical-section` |
| SHA-256 | sha2's software backend (`--cfg sha2_backend="soft"`) |
