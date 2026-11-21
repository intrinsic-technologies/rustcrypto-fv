import Standards.SECG.ECC.Curve
import Standards.SECG.ECC.Encoding

/-!
# Prime-field keys and shared secrets

Private scalar validation, public-key derivation, and raw ECDH (SEC 1 v2.0, §§3.2.1 and 3.3.1).
The caller supplies valid domain parameters.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace Standards.SECG.ECC.Keys

open Curve Encoding

/--
Decode a big-endian secret scalar in `1 ≤ d < n`. Its octet width is the subgroup order's
bit length rounded up to a whole octet (SEC 1 v2.0, Appendix C.4).
-/
def decodeSecret (domain : Domain) (input : ByteArray) : Option Nat :=
  let d := octetsToNat input
  let length := (domain.n.log2 + 8) / 8
  if input.size == length && 0 < d && d < domain.n then some d else none

/--
Derive the public key `dG` from the supplied big-endian secret scalar, returning
`none` unless `1 ≤ d < n` (SEC 1 v2.0, §3.2.1). Scalar generation is left to the caller.
-/
def publicKey (domain : Domain) (input : ByteArray) : Option Point := do
  let d ← decodeSecret domain input
  return scalarMul domain d domain.G

/--
Raw ECDH: return the big-endian x-coordinate of `dQ`, without a KDF (SEC 1 v2.0, §3.3.1).
The output is the field element encoding of SEC 1 v2.0, §2.3.5. Reject invalid scalars and an
identity result. The caller supplies a valid peer key.
-/
def sharedSecret (domain : Domain) (secret : ByteArray) (peer : Point) : Option ByteArray := do
  let d ← decodeSecret domain secret
  match scalarMul domain d peer with
  | .infinity => none
  | .affine x _ => some (natToOctets ((domain.p.log2 + 8) / 8) x)

end Standards.SECG.ECC.Keys
