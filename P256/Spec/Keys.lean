import P256.Spec.KeysEncoding
import P256.Spec.Arith

/-!
# P-256 key functions

The specifications of p256's key functions `SecretKey::public_key` and
`PublicKey::from_sec1_bytes`. Each specification takes the slices of its entry point, `inputs`, in
order, and gives the bytes its result is written as: a `ByteArray` for a function that cannot fail,
an `Option ByteArray` for one that can, `none` being the crate's own error.

Arguments and results are as `program/src/keys.rs` passes them: a secret key is 32 octets
big-endian (`secretOfBytes`), a public key an SEC 1 encoding, read by the crate's decoder
(`Points.decodePublicKey`) and written uncompressed. That a slice is the bytes of a value of its
Rust argument (a valid secret key, a public key) is a premise of the call, stated per entry point
with `Arith.slices` and the checks of each argument's family; the argument decoders read any
bytes, so every specification is total. A function's own checks are not premises: its decoders keep
their errors.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace P256.Spec.Keys

open Standards.SECG.ECC Standards.RFC

/-! ## Arguments -/

/--
A secret key argument: its 32 octets read big-endian, the `d` of SEC 1 v2.0 §3.2.1
(`Arith.isNonZeroScalar` admits exactly `1 ≤ d < n`)
-/
def secretArgument (bytes : ByteArray) : Nat := Arith.uint bytes

/-! ## Results -/

/-- The uncompressed SEC 1 encoding of `point`, as the wrappers write a public key -/
def uncompressed (point : Curve.Point) : ByteArray := encodePoint false point

/-! ## Secret keys -/

/-- `SecretKey::public_key`: the public key `dG` of the secret key `d` (SEC 1 v2.0 §3.2.1) -/
def publicKeyOfSecret (inputs : Array ByteArray) : ByteArray :=
  uncompressed (publicPoint (secretArgument (Arith.argument inputs 0)))

/-! ## Public keys -/

/--
`PublicKey::from_sec1_bytes`: the public key of an SEC 1 encoding (`Points.decodePublicKey`: a point
other than the identity, the compact form included), uncompressed; `none` otherwise
-/
def publicKeyFromSec1 (inputs : Array ByteArray) : Option ByteArray :=
  (P256.Spec.Points.decodePublicKey (Arith.argument inputs 0)).map uncompressed

end P256.Spec.Keys
