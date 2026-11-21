import P256.Spec.Keys
import P256.Spec.Ecdsa
import P256.Spec.Ecdh
import P256.Spec.Generate

/-!
# What the slices of each entry point must hold

For each one-function entry point, the premise of its call that its slices are the bytes of values
of its Rust arguments (`Arith.slices` and the checks of each argument's family), and for
`SigningKey::generate_from_rng` that its random bytes reach an accepted block. The wrappers check
none of it; the tests import this module, which needs no program image.
-/

set_option autoImplicit false

namespace P256.Spec.Functions

/--
What the slices of `p256_public_key_from_sec1_bytes` must hold to be the arguments of
`PublicKey::from_sec1_bytes`
-/
def publicKeyFromSec1BytesArguments : Array ByteArray → Bool := Arith.slices [Arith.anyBytes]

/--
What the slices of `p256_projective_point_add` must hold to be the arguments of
`ProjectivePoint::add`. Each is decoded to an affine point and made projective
(`ProjectivePoint::from`), so the operands have `z = 1` or are the identity `(0, 1, 0)`; operands
with any other `z` are not covered
-/
def projectivePointAddArguments : Array ByteArray → Bool :=
  Arith.slices [Points.isAffineEncoding, Points.isAffineEncoding]

/--
What the slices of `p256_signing_key_try_sign` must hold to be the arguments of `Signer::try_sign`
for `SigningKey` at `Signature`
-/
def signingKeyTrySignArguments : Array ByteArray → Bool :=
  Arith.slices [Arith.isNonZeroScalar, Arith.anyBytes]

/--
What the slices of `p256_verifying_key_verify` must hold to be the arguments of
`Verifier<Signature>::verify` for `VerifyingKey`
-/
def verifyingKeyVerifyArguments : Array ByteArray → Bool :=
  Arith.slices [Ecdsa.isVerifyingKey, Ecdsa.isSignature, Arith.anyBytes]

/--
What the slices of `p256_signature_from_slice` must hold to be the arguments of
`Signature::from_slice`
-/
def signatureFromSliceArguments : Array ByteArray → Bool := Arith.slices [Arith.anyBytes]

/--
What the slices of `p256_signing_key_generate_from_rng` must hold to be the arguments of
`Generate::generate_from_rng` for `SigningKey`: one slice, the random bytes, which hold a 32-byte
block the draw accepts before they run out (`Ecdh.hasRandomNonZeroScalar`), so that the generator
never fails
-/
def signingKeyGenerateFromRngArguments (inputs : Array ByteArray) : Bool :=
  Arith.slices [Arith.anyBytes] inputs && Ecdh.hasRandomNonZeroScalar inputs

/--
What the slices of `p256_ecdh_diffie_hellman` must hold to be the arguments of
`ecdh::diffie_hellman`
-/
def ecdhDiffieHellmanArguments : Array ByteArray → Bool :=
  Arith.slices [Arith.isNonZeroScalar, Points.isAffineEncoding]

end P256.Spec.Functions
