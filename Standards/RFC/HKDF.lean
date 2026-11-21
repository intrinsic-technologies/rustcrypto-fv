import Standards.NIST.SHA1
import Standards.NIST.SHA2
import Standards.RFC.HMAC

/-!
# HMAC-based extract-and-expand key derivation

HKDF from RFC 5869, §§2.2–2.3, parameterized by the hash function, and its instances at SHA-1,
SHA-256, SHA-384, and SHA-512.

Source: https://www.rfc-editor.org/rfc/rfc5869.html
-/

set_option autoImplicit false

namespace Standards.RFC.HKDF

open Standards.NIST.SHA2

/-- The hash function HKDF is instantiated with (RFC 5869, §2.2, `Hash`) -/
structure Hash where
  /-- The hash of an octet string -/
  hash : ByteArray → ByteArray
  /-- The block size in octets, which HMAC needs (RFC 2104, §2, `B`) -/
  blockBytes : Nat
  /-- The output length in octets (RFC 5869, §2.2, `HashLen`) -/
  hashLen : Nat

/-- HKDF's hash at SHA-256 (FIPS 180-4, §1, Figure 1) -/
def Hash.sha256 : Hash := ⟨SHA256.hashBytes, 64, 32⟩

/--
`PRK = HMAC-Hash(salt, IKM)`. An empty salt keys HMAC as the optional all-zero salt does
(RFC 5869, §2.2; RFC 2104, §2 pads the key with zeros).
-/
def extract (H : Hash) (salt ikm : ByteArray) : ByteArray :=
  HMAC.hmac H.hash H.blockBytes salt ikm

/--
HKDF-Expand (RFC 5869, §2.3)

Input: pseudorandom key `prk`, context `info`, and output length `L` in octets
Output: the first `L` octets of `T`, or `none` when `L` exceeds the limit `255 * HashLen`

1. Set `N = ceil(L / HashLen)` and `T(0)` to the empty string
2. For `i` from 1 to `N`, set `T(i) = HMAC-Hash(PRK, T(i-1) | info | i)`, with `i` as one octet
3. Return the first `L` octets of `T = T(1) | ... | T(N)`
-/
def expand (H : Hash) (prk info : ByteArray) (L : Nat) : Option ByteArray :=
  if L > 255 * H.hashLen then none else
  let N := (L + H.hashLen - 1) / H.hashLen
  let T := Id.run do
    let mut T := ByteArray.empty
    let mut previous := ByteArray.empty
    for i in [1:N + 1] do
      previous := HMAC.hmac H.hash H.blockBytes prk (previous ++ info ++ ⟨#[UInt8.ofNat i]⟩)
      T := T ++ previous
    return T
  some (T.extract 0 L)

end Standards.RFC.HKDF
