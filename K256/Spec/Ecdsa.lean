import K256.Spec.Secp256k1
import Standards.NIST.SHA2
import Standards.RFC.DeterministicSigning

/-!
# k256's ECDSA

What the `k256` 0.14.0 ECDSA functions compute: ecdsa 0.17.0's generic signing, verification
and fixed-size signature encoding at secp256k1 (`k256::ecdsa`), with SHA-256 as the
curve's digest (`DigestAlgorithm`, `src/ecdsa.rs:116-119`) and `EcdsaCurve::NORMALIZE_S = true`
(`src/ecdsa.rs:104-106`).

Signing is SEC 1 v2.0, §4.1.3 with the nonce of RFC 6979, §3.2 and HMAC-SHA-256, then low-`s`
normalization (BIP 62). Verification is SEC 1 v2.0, §4.1.4, and also refuses an `s` above `n / 2`.
The fixed-size signature is `r ‖ s`, 32 bytes each, big-endian.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace K256.Spec.Ecdsa

open Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2
open Standards.RFC.DeterministicSigning

/--
The scalars `(r, s)` of a signature `r ‖ s` as `Signature::from_slice` and `Signature::from_bytes`
accept it (`ecdsa-0.17.0/src/lib.rs:212-216`, `200-205` and `237-246`): the bytes are exactly 64
(`from_slice`'s length check; `from_bytes` takes 64 by its type), split into two 32-byte halves,
`r` then `s`, each read as a big-endian integer (SEC 1 v2.0, §2.3.8, `Encoding.octetsToNat`), and
each in `[1, n − 1]` (`from_scalars`: below `n`, by `ScalarValue::from_slice`, and nonzero), the
range SEC 1 v2.0, §4.1.4 step 1 requires of a signature (`ECDSA.verifyDigest`); `none` otherwise.
The fixed-size form itself is not SEC 1's: ecdsa's `Signature` documentation names it IEEE P1363's
(`src/lib.rs:160-170`).
-/
def signatureScalars (signature : ByteArray) : Option (Nat × Nat) :=
  let r := Encoding.octetsToNat (signature.extract 0 32)
  let s := Encoding.octetsToNat (signature.extract 32 64)
  let n := Secp256k1.domain.n
  if signature.size = 64 ∧ 0 < r ∧ r < n ∧ 0 < s ∧ s < n then some (r, s) else none

/-- The 64 bytes `r ‖ s`, 32 big-endian bytes each (`Signature::to_bytes`) -/
def signatureBytes (r s : Nat) : ByteArray := Encoding.natToOctets 32 r ++ Encoding.natToOctets 32 s

/--
Low-`s` normalization (`Signature::normalize_s`, `ecdsa-0.17.0/src/lib.rs:305-310`): `s` above
`n / 2` (rounded down, `IsHigh`) is replaced by `n − s`, which gives an equally valid signature
(BIP 62, "Low S values in signatures")
-/
def normalizeS (r s : Nat) : ByteArray :=
  let n := Secp256k1.domain.n
  signatureBytes r (if s > n / 2 then n - s else s)

/--
The first ECDSA signature `(r, s)` within `attempts` RFC 6979 nonce candidates (RFC 6979, §3.2)
for the secret scalar `d` and the SHA-256 digest of the message, with HMAC-SHA-256 nonces and
signing as in SEC 1 v2.0, §4.1.3; `none` if no candidate within `attempts` gives a signature
-/
def signatureWithin (d : Nat) (message : ByteArray) (attempts : Nat) : Option (Nat × Nat) :=
  let digest := SHA256.hashBytes message
  let signWithNonce := fun k => ECDSA.signWithNonce Secp256k1.domain d k digest
  Signing.signWithin SHA256.hashBytes 64 32 Secp256k1.domain.n signWithNonce d digest attempts

/--
RFC 6979's nonce search signs the message under the secret key, when the 32 bytes are a valid
secret scalar (`Keys.decodeSecret`), after finitely many candidates. Its failure is RFC 6979 §3.2
step h.3's retry loop running forever, which the crate implements as an unbounded loop
(`ecdsa::hazmat::sign_prehashed_rfc6979`, `ecdsa-0.17.0/src/hazmat.rs:114-123`).
-/
def NonceSearchSucceeds (secret message : ByteArray) : Prop :=
  ∀ d, Keys.decodeSecret Secp256k1.domain secret = some d →
    ∃ attempts, (signatureWithin d message attempts).isSome

/--
The signature `Signer::try_sign` gives for a 32-byte big-endian secret scalar `1 ≤ d < n` and a
message: the low-`s` normalized (`normalizeS`) signature that RFC 6979 and SEC 1 v2.0, §4.1.3 give
with SHA-256, as `r ‖ s`. Empty for any other secret, or if no nonce candidate within `2^512`
gives a signature: `2^512` is the number of HMAC states `(K, V)` of RFC 6979, so a search that
finds none within it never finds one.
-/
def signature (secret message : ByteArray) : ByteArray :=
  match Keys.decodeSecret Secp256k1.domain secret with
  | none => ByteArray.empty
  | some d =>
    match signatureWithin d message (2 ^ 512) with
    | some (r, s) => normalizeS r s
    | none => ByteArray.empty

/--
Whether `Verifier::verify` accepts the signature `r ‖ s` (`signatureScalars`) of a message under a
public key that `Secp256k1.decodePublicKey` decodes: `s ≤ n / 2` (`NORMALIZE_S`, the low-S rule of
BIP 62 that k256's README documents) and SEC 1 v2.0, §4.1.4 accepts it with SHA-256
-/
def verifies (publicKey message signature : ByteArray) : Bool :=
  match Secp256k1.decodePublicKey publicKey, signatureScalars signature with
  | some key, some (r, s) =>
    s ≤ Secp256k1.domain.n / 2 &&
      ECDSA.verify Secp256k1.domain SHA256.hashBytes key message (r, s)
  | _, _ => false

end K256.Spec.Ecdsa
