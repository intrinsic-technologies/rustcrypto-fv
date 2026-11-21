import P256.Spec.Arith
import P256.Spec.Points
import Standards.RFC.DeterministicSigning.AdditionalData

/-!
# ECDSA/P-256: signing, verification and raw signatures

The specifications of the ECDSA entry points (`program/src/signatures.rs`): ECDSA over P-256 with
SHA-256 (ecdsa 0.17.0 at `NistP256`), built on SEC 1 v2.0 §4.1 (`Standards.SECG.ECC`), RFC 6979 §3.2
nonces (`Standards.RFC.DeterministicSigning.Signing.signWithin`'s procedure, taken through the
equivalent §3.6 form `AdditionalData.signWithin` with empty additional data), and the raw `r ‖ s`
form (`decodeSignature`), which `Signature::from_slice` reads and every signature argument uses.

Each specification takes the call's input slices in order and gives the result bytes, or `none` for
the crate's error or a signature that does not verify. The checks (`isVerifyingKey`, `isSignature`)
are what a slice must hold, premises of the call (`Spec/Program.lean`, `ValidCall`); the value
decoders read any bytes. The signer cannot fail: the call never returns when no number of RFC 6979
candidates gives a signature (`NeverSigns`, §3.2 h.3), and otherwise returns the signature the
search ends with (`signMessage`); both rest on the bounded search `signMessageWithin`.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace P256.Spec.Ecdsa

open Standards.SECG.ECC Standards.RFC.DeterministicSigning
open P256.Spec.Operations
open P256.Spec.Arith (argument)

/-- The subgroup order `n` of P-256 (SP 800-186, §3.2.1.3) -/
def order : Nat := domain.n

/-! ## Arguments and encodings -/

/--
A secret key argument: its scalar `d` (SEC 1's `decodeSecret`, which `Arith.isNonZeroScalar`
admits), 0 for bytes it rejects
-/
def secretValue (bytes : ByteArray) : Nat := (Keys.decodeSecret domain bytes).getD 0

/--
The public point of a 65-byte uncompressed SEC 1 key on the curve, not the identity (SEC 1 v2.0,
§§2.3.4 and 3.2.2.1), else `none`; the 65-byte length is the wrapper's choice of form
-/
def decodePublicKey (bytes : ByteArray) : Option Curve.Point :=
  if bytes.size = 65 then P256.Spec.Points.decodePublicKey bytes else none

/--
A verifying key: 65 bytes that `VerifyingKey::from_sec1_bytes` accepts, an uncompressed SEC 1
point on the curve (SEC 1 v2.0, §§2.3.4 and 3.2.2.1); the wrapper builds the key with that
function, and a call's contract requires the bytes to be accepted, so its errors are not part of
verification (the theorem on decoding is `PublicKey::from_sec1_bytes`'s)
-/
def isVerifyingKey (bytes : ByteArray) : Bool := (decodePublicKey bytes).isSome

/-- A verifying key argument: its point (`isVerifyingKey` admits it), the identity otherwise -/
def keyValue (bytes : ByteArray) : Curve.Point := (decodePublicKey bytes).getD .infinity

/--
`(r, s)` of a 64-byte `r ‖ s`, 32 octets big-endian each, with `1 ≤ r, s < n`, else `none`: the
range SEC 1 v2.0 §4.1.4 step 1 requires of `r` and `s` (both in `[1, n − 1]`), which
`Signature::from_slice` checks. Each half is read with `Keys.decodeSecret`, which checks the same
range, `1 ≤ x < n`, at the same 32-octet width (SEC 1 v2.0 §3.2.1). The specification of
`Signature::from_slice` (`signatureFromSlice`) and the check and value of every signature argument
(`isSignature`, `signatureValue`) are built on it
-/
def decodeSignature (bytes : ByteArray) : Option (Nat × Nat) :=
  if bytes.size = 64 then do
    let r ← Keys.decodeSecret domain (bytes.extract 0 32)
    let s ← Keys.decodeSecret domain (bytes.extract 32 64)
    some (r, s)
  else none

/--
A signature: what `Signature::from_slice` accepts, 64 bytes `r ‖ s` with `1 ≤ r, s < n`; the
wrapper builds the signature with that function, whose errors belong to its own theorem
-/
def isSignature (bytes : ByteArray) : Bool := (decodeSignature bytes).isSome

/-- A signature argument: its `(r, s)` (`isSignature` admits it), `(0, 0)` otherwise -/
def signatureValue (bytes : ByteArray) : Nat × Nat := (decodeSignature bytes).getD (0, 0)

/-- The integers `(r, s)` as one string of two 32-byte big-endian halves -/
def encodeFixed (signature : Nat × Nat) : ByteArray := encodeSignature signature

/-- The bytes of a `Signature`, `r ‖ s`: 64 -/
def signatureBytes : Nat := 64

/-! ## Signing -/

/--
ECDSA signing with the nonce `k` (SEC 1 v2.0, §4.1.3, `ECDSA.signWithNonce`): `(r, s)`, or `none`
when `kG` is the identity or `r` or `s` is zero. The digest is the prehash, of any length, of which
the leftmost 256 bits are used (§4.1.3, step 5). No low-`s` normalization: `NistP256`'s
`NORMALIZE_S` is false (p256 `src/ecdsa.rs`)
-/
def signWithNonce (secret nonce : Nat) (prehash : ByteArray) : Option (Nat × Nat) :=
  ECDSA.signWithNonce domain secret nonce prehash

/--
The first signature of at most `attempts` RFC 6979 nonce candidates for the secret `d`, the
prehash `h1` and the additional data `k'` (RFC 6979, §§3.2 and 3.6, with HMAC-SHA-256, as
`NistP256`'s `DigestAlgorithm` is SHA-256), or `none` if none of them gives one. RFC 6979 takes
`bits2octets(h1)` from the leftmost 256 bits of a prehash of any length (§2.3.4). The signer of
this specification passes the 32-byte SHA-256 digest of the message; a prehash of 2^29 bytes or
more, on which the crate panics (rfc6979 0.6.0 `bits2int`), never reaches it.
-/
def rfc6979Within (attempts secret : Nat) (prehash extra : ByteArray) : Option (Nat × Nat) :=
  AdditionalData.signWithin hash hashBlockBytes hashDigestBytes order
    (fun nonce => signWithNonce secret nonce prehash) secret prehash extra attempts

/--
The signer's result within at most `attempts` RFC 6979 candidates: `some (some bytes)`, the
signature `r ‖ s`, or `none` while no candidate so far gives one
-/
def signedWithin (attempts secret : Nat) (prehash extra : ByteArray) :
    Option (Option ByteArray) :=
  (rfc6979Within attempts secret prehash extra).map fun signed => some (encodeFixed signed)

/--
`Signer::try_sign` for `SigningKey` at `Signature`, within `attempts` candidates: the secret key,
then the message, whose SHA-256 is signed with RFC 6979 and no additional data
-/
def signMessageWithin (attempts : Nat) (inputs : Array ByteArray) : Option (Option ByteArray) :=
  signedWithin attempts (secretValue (argument inputs 0)) (hash (argument inputs 1)) .empty

/--
No number of RFC 6979 candidates gives the message signer a signature, so its search never ends
(RFC 6979 §3.2 h.3) and the call never returns
-/
def NeverSigns (inputs : Array ByteArray) : Prop :=
  ∀ attempts, signMessageWithin attempts inputs = none

open Classical in
/--
The bytes the message signer returns when its search ends (`NeverSigns` fails): the signature
`r ‖ s` that some number of candidates gives. Every number that gives one gives the same, since a
search that has found a result keeps it (`Signing.signingAttempts`), so the choice is the signature
the search ends with; no bytes when no number gives one
-/
noncomputable def signMessage (inputs : Array ByteArray) : ByteArray :=
  if found : ∃ attempts bytes, signMessageWithin attempts inputs = some (some bytes) then
    Classical.choose (Classical.choose_spec found)
  else .empty

/-! ## Verification -/

/--
ECDSA verification of `(r, s)` on a prehash of any length under the point `Q` (SEC 1 v2.0, §4.1.4,
`ECDSA.verifyDigest`): high and low `s` are both accepted, as `NORMALIZE_S` is false
-/
def verifies (key : Curve.Point) (prehash : ByteArray) (signature : Nat × Nat) : Bool :=
  ECDSA.verifyDigest domain key prehash signature

/--
The verifier's result on the key argument `key`, the `Signature` argument `encoded` (`r ‖ s`) and
the prehash: no bytes for a valid signature, `none` for one that does not verify
-/
def verifyWith (key encoded prehash : ByteArray) : Option ByteArray :=
  if verifies (keyValue key) prehash (signatureValue encoded) then some .empty else none

/--
`Verifier<Signature>::verify` for `VerifyingKey`: the key, the signature, then the message, whose
SHA-256 is verified (`verifyWith`)
-/
def verifyMessage (inputs : Array ByteArray) : Option ByteArray :=
  verifyWith (argument inputs 0) (argument inputs 1) (hash (argument inputs 2))

/-! ## The signature types -/

/--
`Signature::from_slice`: the one slice read as `r ‖ s` by `decodeSignature`, and on success the
signature written back as `r ‖ s`, which gives the same 64 bytes; else the crate's error. The
crate's steps (ecdsa 0.17.0 `src/lib.rs:200-246`), each a check of `decodeSignature`:

1. length: the slice must be exactly 64 bytes, twice the 32 bytes of `FieldBytes`
   (`<&SignatureBytes>::try_from` in `from_slice`), else the error;
2. split: its first 32 bytes are `r` and its last 32 bytes `s` (`from_bytes`);
3. range: each is read big-endian (SEC 1 v2.0 §2.3.8) and must be below `n`
   (`ScalarValue::from_slice` in `from_scalars`), else the error;
4. nonzero: neither may be 0 (`from_scalars`), else the error.

Steps 3 and 4 together are the range `1 ≤ r, s < n` of SEC 1 v2.0 §4.1.4 step 1. Every failure
is the same `signature::Error`, so the specification has one failure, `none`
-/
def signatureFromSlice (inputs : Array ByteArray) : Option ByteArray :=
  (decodeSignature (argument inputs 0)).map encodeFixed

end P256.Spec.Ecdsa
