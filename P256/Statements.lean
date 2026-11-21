import P256.Spec

/-!
# p256 0.14.0

Theorems about the compiled machine code of p256 0.14.0, one per operation. Each says that a
well-formed call returns (apart from `try_sign`'s never-returns branch) and produces what the
specification in `P256/Spec/` computes; the specifications are built on the standards in
`Standards/`.

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| `PublicKey::from_sec1_bytes` | `p256_public_key_from_sec1_bytes_writes_public_key_or_rejects_encoding` | `Keys.publicKeyFromSec1` | SEC 1 v2.0 §2.3.3–§2.3.4 |
| `Signer::try_sign` for `SigningKey` | `p256_signing_key_try_sign_writes_signature_or_never_returns` | `Ecdsa.signMessage` | SEC 1 v2.0 §4.1.3; RFC 6979 §3.2 |
| `Verifier::verify` for `VerifyingKey` | `p256_verifying_key_verify_accepts_signature_or_rejects_signature` | `Ecdsa.verifyMessage` | SEC 1 v2.0 §4.1.4 |
| `Signature::from_slice` | `p256_signature_from_slice_writes_signature_or_rejects_bytes` | `Ecdsa.signatureFromSlice` | SEC 1 v2.0 §2.3.8, §4.1.4 |
| `Generate::generate_from_rng` for `SigningKey` | `p256_signing_key_generate_from_rng_writes_signing_key` | `Generate.generatedSigningKey` | SEC 1 v2.0 §3.2.1 |
| `ecdh::diffie_hellman` | `p256_ecdh_diffie_hellman_writes_shared_secret` | `Ecdh.diffieHellman` | SEC 1 v2.0 §3.3.1 |

How to read the theorem statements, the deliberate differences from the standards and the build are
in `P256/README.md`.
-/

set_option warn.sorry false
set_option autoImplicit false

namespace P256.Statements

open P256.Spec Prelude X86 P256.Spec.Program.Routines

/--
`PublicKey::from_sec1_bytes` (elliptic-curve 0.14.3, `src/public_key.rs:126-133`): decodes a SEC 1
encoding into a curve point other than the identity.

If `Keys.publicKeyFromSec1` accepts `bytes` (`02`/`03 ‖ x` or `04 ‖ x ‖ y` of a point on the
curve, SEC 1 v2.0 §2.3.3–§2.3.4, or the crate's compact `05 ‖ x`), the call returns status 0 and
writes the point uncompressed, `04 ‖ x ‖ y`. Otherwise (the identity `00`, another tag or
length, or no point) it returns `invalidPublicKeyStatus` and writes nothing to the output. The
compact form is not SEC 1's (`P256/README.md`, Deliberate differences from the standards).
-/
theorem p256_public_key_from_sec1_bytes_writes_public_key_or_rejects_encoding
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall publicKeyFromSec1Bytes initial [bytes]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Keys.publicKeyFromSec1 #[bytes] with
      | some result =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion publicKeyFromSec1Bytes initial [bytes], allocatorStateRegion,
            randomSourceRegion, callStack publicKeyFromSec1Bytes initial] ∧
        readOutput publicKeyFromSec1Bytes initial final = .ok result
      | none =>
        FailureStatus final invalidPublicKeyStatus ∧
        MemoryWriteFrame initial final
          #v[allocatorStateRegion, randomSourceRegion,
            callStack publicKeyFromSec1Bytes initial] := by
  sorry

open Classical in
/--
`Signer::try_sign` for `SigningKey` at `Signature` (ecdsa 0.17.0, `src/signing.rs:185-187`): hashes
`msg` with SHA-256 and signs the digest by ECDSA under the secret key `signingKey`, with RFC 6979's
deterministic nonce.

If no RFC 6979 nonce candidate ever gives a signature (`Ecdsa.NeverSigns`, RFC 6979 §3.2 h.3's
retry), the call never returns (`NeverReturns`). Otherwise it returns and writes
`Ecdsa.signMessage`, `r ‖ s` with no low-`s` normalization (SEC 1 v2.0 §4.1.3; RFC 6979 §3.2).
-/
theorem p256_signing_key_try_sign_writes_signature_or_never_returns
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {signingKey msg : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyTrySign initial [signingKey, msg]) :
    if Ecdsa.NeverSigns #[signingKey, msg] then NeverReturns initial else
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signingKeyTrySign initial [signingKey, msg], allocatorStateRegion,
          randomSourceRegion, callStack signingKeyTrySign initial] ∧
      readOutput signingKeyTrySign initial final = .ok (Ecdsa.signMessage #[signingKey, msg]) := by
  sorry

/--
`Verifier<Signature>::verify` for `VerifyingKey` (ecdsa 0.17.0, `src/verifying.rs:170-172`): checks
the ECDSA signature `signature` (`r ‖ s`) on the SHA-256 of `msg` under `verifyingKey` (65 bytes,
uncompressed SEC 1); a high `s` is accepted.

If `Ecdsa.verifyMessage` accepts (SEC 1 v2.0 §4.1.4), the call returns status 0 and writes a result
of no bytes, only the length 0. Otherwise it returns `invalidSignatureStatus` and writes nothing to
the output.
-/
theorem p256_verifying_key_verify_accepts_signature_or_rejects_signature
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {verifyingKey signature msg : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall verifyingKeyVerify initial [verifyingKey, signature, msg]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Ecdsa.verifyMessage #[verifyingKey, signature, msg] with
      | some result =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion verifyingKeyVerify initial [verifyingKey, signature, msg],
            allocatorStateRegion, randomSourceRegion, callStack verifyingKeyVerify initial] ∧
        readOutput verifyingKeyVerify initial final = .ok result
      | none =>
        FailureStatus final invalidSignatureStatus ∧
        MemoryWriteFrame initial final
          #v[allocatorStateRegion, randomSourceRegion, callStack verifyingKeyVerify initial] := by
  sorry

/--
`Signature::from_slice` (ecdsa 0.17.0, `src/lib.rs:212-216`): reads a 64-byte raw signature, `r`
then `s`, each 32 bytes big-endian.

If `Ecdsa.signatureFromSlice` accepts the bytes (`r` and `s` both in `[1, n − 1]`; SEC 1 v2.0
§2.3.8, §4.1.4 step 1), the call returns status 0 and writes the signature, the same 64 bytes.
Otherwise it returns `invalidSignatureBytesStatus` and writes nothing to the output.
-/
theorem p256_signature_from_slice_writes_signature_or_rejects_bytes
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signatureFromSlice initial [bytes]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Ecdsa.signatureFromSlice #[bytes] with
      | some result =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion signatureFromSlice initial [bytes], allocatorStateRegion,
            randomSourceRegion, callStack signatureFromSlice initial] ∧
        readOutput signatureFromSlice initial final = .ok result
      | none =>
        FailureStatus final invalidSignatureBytesStatus ∧
        MemoryWriteFrame initial final
          #v[allocatorStateRegion, randomSourceRegion, callStack signatureFromSlice initial] := by
  sorry

/--
`Generate::generate_from_rng` for `SigningKey` (crypto-common 0.2.2, `src/generate.rs:17-20`),
calling `try_generate_from_rng` (ecdsa 0.17.0, `src/signing.rs:134-138`): draws an ECDSA signing
key from the caller's random bytes `randomBytes`.

The call writes `Generate.generatedSigningKey`: the secret scalar `d`, the first 32-byte block that,
read big-endian, is in `[1, n − 1]`, then its verifying key `dG`, uncompressed, 97 bytes in all
(SEC 1 v2.0 §3.2.1).
-/
theorem p256_signing_key_generate_from_rng_writes_signing_key
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {randomBytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyGenerateFromRng initial [randomBytes]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signingKeyGenerateFromRng initial [randomBytes], allocatorStateRegion,
          randomSourceRegion, callStack signingKeyGenerateFromRng initial] ∧
      readOutput signingKeyGenerateFromRng initial final =
        .ok (Generate.generatedSigningKey #[randomBytes]) := by
  sorry

/--
`ecdh::diffie_hellman` (elliptic-curve 0.14.3, `src/ecdh.rs:61-71`): raw ECDH, the x-coordinate of
the secret scalar `secretKey` times the other party's point `publicKey`, with no key derivation.

The call writes `Ecdh.diffieHellman`, 32 bytes big-endian (SEC 1 v2.0 §3.3.1). For the identity as
`publicKey` it writes 32 zero bytes, where SEC 1 §3.3.1 outputs "invalid" (`P256/README.md`,
Deliberate differences from the standards).
-/
theorem p256_ecdh_diffie_hellman_writes_shared_secret
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {secretKey publicKey : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall ecdhDiffieHellman initial [secretKey, publicKey]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion ecdhDiffieHellman initial [secretKey, publicKey], allocatorStateRegion,
          randomSourceRegion, callStack ecdhDiffieHellman initial] ∧
      readOutput ecdhDiffieHellman initial final =
        .ok (Ecdh.diffieHellman #[secretKey, publicKey]) := by
  sorry

end P256.Statements
