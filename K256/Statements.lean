import K256.Spec

set_option warn.sorry false

/-!
# k256 0.14.0

Theorems about the compiled machine code of k256 0.14.0, one per operation. Each says that a
well-formed call returns (apart from `try_sign`'s never-returns branch) and produces what the
specification in `K256/Spec/` computes; the specifications are built on the standards in
`Standards/`.

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| `Signer::try_sign` for `SigningKey` | `k256_signing_key_try_sign_writes_low_s_signature_or_never_returns` | `Ecdsa.signature` | SEC 1 v2.0 §4.1.3, RFC 6979 §3.2, low `s` (BIP 62) |
| `Verifier::verify` for `VerifyingKey` | `k256_verifying_key_verify_accepts_signature_or_rejects_signature` | `Ecdsa.verifies` | SEC 1 v2.0 §4.1.4, low `s` (BIP 62) |
| `Signature::from_slice` | `k256_signature_from_slice_writes_signature_or_rejects_bytes` | `Ecdsa.signatureScalars`, `Ecdsa.signatureBytes` | SEC 1 v2.0 §§2.3.7–2.3.8, §4.1.4 step 1 |
| `Generate::generate_from_rng` for `SigningKey` | `k256_signing_key_generate_from_rng_writes_signing_key` | `Secp256k1.generatedSigningKey` | SEC 1 v2.0 §3.2.1 |
| `PublicKey::from_sec1_bytes` | `k256_public_key_from_sec1_bytes_writes_public_key_or_rejects_encoding` | `Secp256k1.decodePublicKey` | SEC 1 v2.0 §2.3.4 |
| `ecdh::diffie_hellman` | `k256_ecdh_diffie_hellman_writes_shared_secret` | `Secp256k1.sharedSecret` | SEC 1 v2.0 §3.3.1 |

How to read the theorem statements, the deliberate differences from the standards and how to build
the verified binary are in `K256/README.md`.
-/

namespace K256.Statements

open K256.Spec K256.Spec.Program Prelude X86 Standards.SECG.ECC Standards.SECG.DomainParameters
  Standards.NIST.SHA2

open Classical in
/--
`Signer::try_sign` for `SigningKey` (ecdsa 0.17.0, `src/signing.rs:185-187`): hashes the message
with SHA-256 and signs the digest with ECDSA and RFC 6979 nonces, then replaces an `s` above `n / 2`
by `n − s`.

If RFC 6979's nonce search succeeds (`Ecdsa.NonceSearchSucceeds`), the call returns and writes
`Ecdsa.signature secret message`, the 64 bytes `r ‖ s`, to the output. Otherwise it never returns
(`NeverReturns`), as RFC 6979 §3.2 step h.3 retries without end; no input reaching this branch is
known. `try_sign` is `Ok` whenever it returns, so the wrapper returns no status.
-/
theorem k256_signing_key_try_sign_writes_low_s_signature_or_never_returns
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {secret message : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyTrySign initial [secret, message]) :
    if ¬ Ecdsa.NonceSearchSucceeds secret message then NeverReturns initial else
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signingKeyTrySign initial,
          Stack.region initial signingKeyTrySign.minStackBytes] ∧
      readOutput signingKeyTrySign initial final = .ok (Ecdsa.signature secret message) := by
  sorry

/--
`Verifier::verify` for `VerifyingKey` (ecdsa 0.17.0, `src/verifying.rs:170-172`): hashes the
message with SHA-256 and checks the ECDSA signature `r ‖ s` against the public key.

If `Ecdsa.verifies publicKey message signature` (`s ≤ n / 2` and SEC 1 v2.0 §4.1.4 accepts), the
call returns status 0; otherwise it returns `signatureErrorStatus`. It writes no output. SEC 1
accepts a high `s`; k256 refuses it (`NORMALIZE_S`, BIP 62's low-`s` rule).
-/
theorem k256_verifying_key_verify_accepts_signature_or_rejects_signature
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {publicKey message signature : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall verifyingKeyVerify initial [publicKey, message, signature]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if Ecdsa.verifies publicKey message signature then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final #v[Stack.region initial verifyingKeyVerify.minStackBytes]
      else
        FailureStatus final signatureErrorStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial verifyingKeyVerify.minStackBytes] := by
  sorry

/--
`Signature::from_slice` (ecdsa 0.17.0, `src/lib.rs:212-216`): reads a 64-byte raw signature, `r`
then `s`, each 32 bytes big-endian.

If `Ecdsa.signatureScalars` accepts the bytes (exactly 64, with `r` and `s` both in `[1, n − 1]`;
SEC 1 v2.0 §§2.3.7–2.3.8, §4.1.4 step 1), the call returns status 0 and writes
`Ecdsa.signatureBytes r s` to the output. Otherwise it returns `signatureErrorStatus` and leaves the
output untouched.
-/
theorem k256_signature_from_slice_writes_signature_or_rejects_bytes
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signatureFromSlice initial [bytes]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Ecdsa.signatureScalars bytes with
      | some (r, s) =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion signatureFromSlice initial,
            Stack.region initial signatureFromSlice.minStackBytes] ∧
        readOutput signatureFromSlice initial final = .ok (Ecdsa.signatureBytes r s)
      | none =>
        FailureStatus final signatureErrorStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial signatureFromSlice.minStackBytes] := by
  sorry

/--
`Generate::generate_from_rng` for `SigningKey` (crypto-common 0.2.2, `src/generate.rs:17-20`),
calling `try_generate_from_rng` (ecdsa 0.17.0, `src/signing.rs:134-138`): draws a new secret scalar
`d` from the random generator and computes its verifying key `d · G`.

The generator serves the caller's bytes `random` in order. The call returns and writes
`Secp256k1.generatedSigningKey random`, 97 bytes: `d`, the first 32-byte block in `[1, n − 1]`, then
`d · G` in its 65-byte uncompressed SEC 1 encoding.
-/
theorem k256_signing_key_generate_from_rng_writes_signing_key
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {random : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyGenerateFromRng initial [random]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signingKeyGenerateFromRng initial,
          Stack.region initial signingKeyGenerateFromRng.minStackBytes] ∧
      readOutput signingKeyGenerateFromRng initial final =
        .ok (Secp256k1.generatedSigningKey random) := by
  sorry

/--
`PublicKey::from_sec1_bytes` (elliptic-curve 0.14.3, `src/public_key.rs:126-133`): reads a public
key from its SEC 1 encoding (SEC 1 v2.0 §2.3.4), uncompressed `04 ‖ x ‖ y` or compressed `02 ‖ x`
or `03 ‖ x`, or from RustCrypto's compact `05 ‖ x`, which is not SEC 1.

If `Secp256k1.decodePublicKey bytes` gives a point, the call returns status 0 and writes the point's
65-byte uncompressed SEC 1 encoding to the output. Otherwise (another tag or length, a point not on
the curve, or the identity) it returns `ellipticCurveErrorStatus` and leaves the output untouched.
-/
theorem k256_public_key_from_sec1_bytes_writes_public_key_or_rejects_encoding
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall publicKeyFromSec1Bytes initial [bytes]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Secp256k1.decodePublicKey bytes with
      | some point =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion publicKeyFromSec1Bytes initial,
            Stack.region initial publicKeyFromSec1Bytes.minStackBytes] ∧
        readOutput publicKeyFromSec1Bytes initial final =
          .ok (Points.encodePoint Secp256k1.domain false point)
      | none =>
        FailureStatus final ellipticCurveErrorStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial publicKeyFromSec1Bytes.minStackBytes] := by
  sorry

/--
`ecdh::diffie_hellman` (elliptic-curve 0.14.3, `src/ecdh.rs:61-71`): computes the x-coordinate of
`d · Q` for the secret scalar `d` and the peer's point `Q`, given as its 33-byte `GroupEncoding`
(compressed SEC 1, the compact `05 ‖ x`, or 33 zero bytes for the identity).

The call returns and writes `Secp256k1.sharedSecret secret publicKey`, 32 bytes: raw ECDH (SEC 1
v2.0 §3.3.1) for a point other than the identity. `Q` may be the identity, which SEC 1 §3.3.1 does
not take and `diffie_hellman` does; the result is then 32 zero bytes.
-/
theorem k256_ecdh_diffie_hellman_writes_shared_secret
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {secret publicKey : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall ecdhDiffieHellman initial [secret, publicKey]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion ecdhDiffieHellman initial,
          Stack.region initial ecdhDiffieHellman.minStackBytes] ∧
      readOutput ecdhDiffieHellman initial final =
        .ok (Secp256k1.sharedSecret secret publicKey) := by
  sorry

end K256.Statements
