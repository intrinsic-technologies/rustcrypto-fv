import Standards.SECG.ECC.Encoding
import Standards.SECG.ECC.Curve

/-!
# Prime-field point encodings

Point serialization, validation, and decompression (SEC 1 v2.0, §§2.3.3–2.3.4 and 3.2.2).
Point encoding and decoding take explicit prime-field curve parameters. Compressed decoding
requires a modular square-root function from the caller. No square-root algorithm is prescribed
here.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace Standards.SECG.ECC.Points

open Curve Encoding

/--
Serialize a prime-field curve point in compressed or uncompressed form; infinity is `0x00`
(SEC 1 v2.0, §2.3.3). Coordinate width is derived from the supplied modulus.
Assumes canonical curve coordinates without checking them.
-/
def encodePoint (domain : Domain) (compressed : Bool) (point : Point) : ByteArray :=
  let length := (domain.p.log2 + 8) / 8
  match point with
  | .infinity => ⟨#[0]⟩
  | .affine x y =>
    if compressed then ⟨#[UInt8.ofNat (2 + y % 2)]⟩ ++ natToOctets length x
    else ⟨#[4]⟩ ++ natToOctets length x ++ natToOctets length y

/--
Octet-string-to-point conversion (SEC 1 v2.0, §2.3.4)

Input: a point encoding for the supplied prime-field curve
Output: the decoded point, or `none` for an invalid or unsupported encoding

The supplied `sqrtMod` function must return a square root for each canonical field element
that has one, and `none` otherwise. Returned roots are reduced modulo `p` and checked before
accepting the point.

Let `length` be the field-element width in octets, derived from `p`.
1. Decode the single octet `0x00` as the identity
2. For a `1 + 2 * length`-byte string starting with `0x04`, parse the coordinates and check `onCurve`
3. For a `1 + length`-byte string starting with `0x02` or `0x03`:
   a. Parse `x` and require `x < p`
   b. Set `α = x³ + ax + b mod p` and obtain a square root `β` using `sqrtMod`
   c. Select `y` from `β` and `−β mod p` to match the prefix parity
   d. Require `y² mod p = α` and the requested parity, then return `(x, y)`; a zero root with
      prefix `0x03` fails (SP 800-186, Appendix E.3)
4. Reject all other encodings, including hybrid form
-/
def decodePoint (domain : Domain) (sqrtMod : Nat → Option Nat) (input : ByteArray) :
    Option Point := do
  if input == ⟨#[0]⟩ then return .infinity
  let p := domain.p
  let length := (p.log2 + 8) / 8
  let tag := input.data[0]?.getD 0
  if input.size == 1 + 2 * length && tag == 4 then
    let point := Point.affine (octetsToNat (input.extract 1 (1 + length)))
      (octetsToNat (input.extract (1 + length) (1 + 2 * length)))
    if onCurve domain point then return point else none
  else if input.size == 1 + length && (tag == 2 || tag == 3) then
    let x := octetsToNat (input.extract 1 (1 + length))
    if x ≥ p then none else
    let square := (x * x * x + domain.a * x + domain.b) % p
    let root := (← sqrtMod square) % p
    let y := if root % 2 == tag.toNat % 2 then root else fieldSub p 0 root
    if y * y % p == square && y % 2 == tag.toNat % 2 then return .affine x y else none
  else none

/--
Decode a canonical nonidentity public key for valid domain parameters (SEC 1 v2.0, §3.2.2.1).
Check subgroup membership with `nQ = O`; for cofactor one, curve membership already implies it.
The supplied `sqrtMod` has the contract specified by `decodePoint` for `domain.p`.
-/
def decodePublicKey (domain : Domain) (sqrtMod : Nat → Option Nat) (input : ByteArray) :
    Option Point := do
  let point ← decodePoint domain sqrtMod input
  match point with
  | .infinity => none
  | .affine _ _ =>
    if domain.h == 1 || scalarMul domain domain.n point == .infinity then some point else none

end Standards.SECG.ECC.Points
