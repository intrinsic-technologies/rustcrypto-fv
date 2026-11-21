import P256.Spec.Arith

/-!
# P-256 points: the group law and SEC 1 point encodings

The specification of primeorder 0.14.0's `AffinePoint` and `ProjectivePoint` and their SEC 1
conversions at p256 0.14.0's `NistP256`. The group law is SEC 1's (`Curve.add`, `Curve.scalarMul`)
over the P-256 domain of SP 800-186; the projective representation is invisible, since every result
is read back through `to_affine`. Point decoding is SEC 1 v2.0 §2.3.4's
(`Standards.SECG.ECC.Points.decodePoint`), to which the crate adds the compact `05 ‖ x` form of
draft-jivsov (the point with `y = min(y, p − y)`), which SEC 1 does not define (`P256/README.md`,
Deliberate differences from the standards).

Byte forms (`program/src/points.rs`, `keys.rs`, `extras.rs`): a point argument is SEC 1 or compact
bytes, which the crate's `Sec1Point::from_bytes` and `FromSec1Point` decode (`decodePoint`); a point
result is `to_sec1_point(false)`, `00` or `04 ‖ x ‖ y` (`encode`); a scalar is 32 big-endian bytes
below `n`. The check `isAffineEncoding` is what a slice must hold, a premise of the call; the
specifications read any bytes.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace P256.Spec.Points

open Standards.SECG.ECC Standards.SECG.ECC.Curve Standards.SECG.ECC.Encoding
open Operations (domain sqrtMod)

/-! ## The curve -/

/-- `x³ + ax + b mod p`, the right-hand side of the P-256 equation (SEC 1 §2.2.1) -/
def curveRhs (x : Nat) : Nat := (x * x * x + domain.a * x + domain.b) % domain.p

/-- `-v mod p` -/
def negElement (value : Nat) : Nat := fieldSub domain.p 0 value

/--
Point decompression (`DecompressPoint::decompress`, primeorder `src/affine.rs`; SEC 1 §2.3.4,
step 2.4): for `x < p`, take the square root `β` of `x³ + ax + b` that p256's `FieldElement::sqrt`
returns, `(x³ + ax + b)^((p+1)/4)` (SP 800-186, Appendix E.3), or nothing if it has none, and the
point `(x, β)` if `β`'s parity is the one asked for, else `(x, −β)`
-/
def decompress (x : Nat) (odd : Bool) : Option Point := do
  if x ≥ domain.p then none
  let root ← sqrtMod (curveRhs x)
  let y := if (root % 2 == 1) == odd then root else negElement root
  return .affine x y

/-- The compact `y` of draft-jivsov: the smaller of `y` and `p − y` (`AffinePoint::to_compact`) -/
def compactY (y : Nat) : Nat := if y > negElement y then negElement y else y

/--
Compact decoding (`DecompactPoint::decompact`): the decompressed point with even `y`, then its
compact `y`; RustCrypto's compact form, which SEC 1 does not define
-/
def decompact (x : Nat) : Option Point :=
  (decompress x false).map fun
    | .affine x y => .affine x (compactY y)
    | .infinity => .infinity

/-! ## SEC 1 encodings -/

/-- The 32 bytes from `start` of `input`, as an integer, big-endian -/
def element (input : ByteArray) (start : Nat) : Nat :=
  octetsToNat (input.extract start (start + 32))

/--
The crate's SEC 1 decoder, `Sec1Point::from_bytes` then `FromSec1Point::from_sec1_point`: SEC 1
v2.0 §2.3.4 (`Standards.SECG.ECC.Points.decodePoint`: the identity `00`, compressed `02`/`03 ‖ x`,
uncompressed `04 ‖ x ‖ y` on the curve), plus the crate's compact `05 ‖ x` (`decompact`), which
SEC 1 does not have; nothing for other bytes or coordinates that give no point
-/
def decodePoint (input : ByteArray) : Option Point :=
  if input.size = 33 ∧ input.data[0]? = some 5 then decompact (element input 1)
  else Standards.SECG.ECC.Points.decodePoint domain sqrtMod input

/-- A `PublicKey`, decoded by `PublicKey::from_sec1_bytes`: a point other than the identity -/
def decodePublicKey (input : ByteArray) : Option Point :=
  match decodePoint input with
  | some .infinity => none
  | point => point

/-- `to_sec1_point(compress)`: `00` for the identity, else SEC 1 §2.3.3's encoding -/
def encodeWith (compress : Bool) (point : Point) : ByteArray :=
  Standards.SECG.ECC.Points.encodePoint domain compress point

/-- The output encoding of a point, `to_sec1_point(false)` -/
def encode (point : Point) : ByteArray := encodeWith false point

/-- The affine `x` as 32 bytes, zero for the identity, which the crate stores as `(0, 0)` -/
def xBytes : Point → ByteArray
  | .infinity => natToOctets 32 0
  | .affine x _ => natToOctets 32 x

/-! ## The group -/

/-- `P + Q` (SEC 1 §2.2.1) -/
def add (left right : Point) : Point := Curve.add domain left right

/-- `kP` -/
def mul (scalar : Nat) (point : Point) : Point := Curve.scalarMul domain scalar point

/-! ## What a slice must hold: the premises of `ValidCall` -/

/--
A SEC 1 or compact point encoding the crate decodes to an `AffinePoint`, `Sec1Point::from_bytes`
then `AffinePoint::from_sec1_point` (`decodePoint`): an `AffinePoint` or `ProjectivePoint`
argument, which the entry point builds from these bytes with those two crate functions
-/
def isAffineEncoding (bytes : ByteArray) : Bool := (decodePoint bytes).isSome

/-! ## Arguments -/

/-- A point of SEC 1 or compact bytes (`decodePoint`), the identity for bytes that are none -/
def pointOf (bytes : ByteArray) : Point := (decodePoint bytes).getD .infinity

/-- Point argument `i` (`isAffineEncoding` admits it) -/
def pointArgument (inputs : Array ByteArray) (i : Nat) : Point := pointOf (Arith.argument inputs i)

/-- Scalar argument `i`, a `NonZeroScalar`: its 32 bytes read big-endian -/
def scalarArgument (inputs : Array ByteArray) (i : Nat) : Nat :=
  Arith.element domain.n (Arith.argument inputs i)

/-! ## Point addition -/

/-- `P + Q`: `ProjectivePoint::add`, both points decoded from their SEC 1 or compact arguments -/
def pointAdd (inputs : Array ByteArray) : ByteArray :=
  encode (add (pointArgument inputs 0) (pointArgument inputs 1))

end P256.Spec.Points
