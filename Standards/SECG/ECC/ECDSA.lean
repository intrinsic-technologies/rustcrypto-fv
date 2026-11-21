import Standards.SECG.ECC.Curve
import Standards.SECG.ECC.Encoding

/-!
# Prime-field ECDSA

Signing with a supplied nonce and verification (SEC 1 v2.0, §§4.1.3–4.1.4).
The caller supplies valid domain parameters, a valid public key, and the selected hash
function.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace Standards.SECG.ECC.ECDSA

open Curve Encoding

/--
Interpret the leftmost `min(bitLength(n), digestBits)` bits of a digest as an unsigned integer
(SEC 1 v2.0, §4.1.3, step 5). Assumes positive subgroup order `order`.
-/
def digestToInt (order : Nat) (digest : ByteArray) : Nat :=
  octetsToNat digest / 2 ^ (8 * digest.size - (order.log2 + 1))

/--
ECDSA signature generation with a supplied nonce (SEC 1 v2.0, §4.1.3)

Input: private scalar `d`, nonce `k`, and message digest
Output: the signature `(r, s)`, or `none` on failure

1. Require `1 ≤ d, k < n`; SEC 1 assumes a valid `d`
2. Compute `R = kG`, rejecting the identity, which valid inputs never produce
3. Set `r = x(R) mod n` and truncate the digest to the subgroup order's bit length
4. Set `s = k⁻¹(e + rd) mod n`
5. Reject zero `r` or `s`; otherwise return `(r, s)` without low-`s` normalization
-/
def signWithNonce (domain : Domain) (secret nonce : Nat)
    (digest : ByteArray) : Option (Nat × Nat) := do
  let n := domain.n
  if secret == 0 || secret ≥ n || nonce == 0 || nonce ≥ n then none else
  match scalarMul domain nonce domain.G with
  | .infinity => none
  | .affine x _ =>
    let r := x % n
    let e := digestToInt n digest
    let s := inverse n nonce * (e + r * secret) % n
    if r == 0 || s == 0 then none else some (r, s)

/--
ECDSA verification on a digest (SEC 1 v2.0, §4.1.4)

Input: valid public key `Q`, message digest, and signature `(r, s)`
Output: whether the signature verifies

1. Require `1 ≤ r, s < n`
2. Set `w = s⁻¹ mod n` and truncate the digest to obtain `e`
3. Set `u₁ = ew mod n` and `u₂ = rw mod n`
4. Compute `R = u₁G + u₂Q` and reject the identity
5. Accept exactly when `x(R) mod n = r`

Both high and low `s` values are accepted.
-/
def verifyDigest (domain : Domain) (key : Point) (digest : ByteArray) (signature : Nat × Nat) :
    Bool :=
  let (r, s) := signature
  let n := domain.n
  if r == 0 || r ≥ n || s == 0 || s ≥ n then false else
  let reciprocal := inverse n s
  let u₁ := digestToInt n digest * reciprocal % n
  let u₂ := r * reciprocal % n
  match add domain (scalarMul domain u₁ domain.G) (scalarMul domain u₂ key) with
  | .infinity => false
  | .affine x _ => x % n == r

/-- ECDSA verification of an octet message using the caller's selected hash function. -/
def verify (domain : Domain) (hash : ByteArray → ByteArray) (key : Point) (message : ByteArray)
    (signature : Nat × Nat) : Bool :=
  verifyDigest domain key (hash message) signature

end Standards.SECG.ECC.ECDSA
