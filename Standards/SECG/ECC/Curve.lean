/-!
# Prime-field elliptic curves

Short-Weierstrass arithmetic over a prime field (SEC 1 v2.0, §§2.1.1 and 2.2.1). Coordinates are
natural-number representatives. The group law requires an odd prime `p`, a nonsingular curve, and
inputs satisfying `onCurve`.

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace Standards.SECG.ECC.Curve

/-- The identity or an affine pair of field representatives. -/
inductive Point where
  | infinity
  | affine (x y : Nat)
  deriving Repr, BEq, DecidableEq

/-- Prime-field Weierstrass domain parameters `(p, a, b, G, n, h)` (SEC 1 v2.0, §3.1.1). -/
structure Domain where
  p : Nat
  a : Nat
  b : Nat
  G : Point
  n : Nat
  h : Nat
  deriving Repr

/-- Canonical field subtraction; reduces both inputs modulo the modulus. -/
def fieldSub (p x y : Nat) : Nat := (x % p + p - y % p) % p

/-- Compute `base^exponent mod modulus` by square-and-multiply. -/
def powMod (modulus base exponent : Nat) : Nat := Id.run do
  let mut result := 1 % modulus
  let mut power := base % modulus
  for i in [:exponent.log2 + 1] do
    if exponent.testBit i then result := result * power % modulus
    power := power * power % modulus
  return result

/--
Inverse of a nonzero residue modulo odd prime `p`; zero maps to zero (SP 800-186, Appendix E.4).
-/
def inverse (p x : Nat) : Nat := powMod p x (p - 2)

/-- Membership in the curve, requiring canonical coordinates for affine points. -/
def onCurve (domain : Domain) : Point → Bool
  | .infinity => true
  | .affine x y => x < domain.p && y < domain.p &&
      y * y % domain.p == (x * x * x + domain.a * x + domain.b) % domain.p

/--
Elliptic-curve addition (SEC 1 v2.0, §2.2.1)

Parameters: a nonsingular short-Weierstrass curve over a field of odd prime order `p`
Input: curve points `P` and `Q` with canonical coordinates
Output: the curve point `P + Q`

1. If either point is the identity, return the other
2. If `P` and `Q` have the same x-coordinate and opposite y-coordinates, return the identity
3. For doubling, set `λ = (3x₁² + a) / (2y₁)`; otherwise set `λ = (y₂ − y₁) / (x₂ − x₁)`
4. Set `x₃ = λ² − x₁ − x₂` and `y₃ = λ(x₁ − x₃) − y₁`, with arithmetic modulo `p`
5. Return `(x₃, y₃)`
-/
def add (domain : Domain) : Point → Point → Point
  | .infinity, right => right
  | left, .infinity => left
  | .affine x₁ y₁, .affine x₂ y₂ =>
    let p := domain.p
    if x₁ == x₂ && (y₁ + y₂) % p == 0 then .infinity else
    let slope := if x₁ == x₂ then
      (3 * x₁ * x₁ + domain.a) * inverse p (2 * y₁) % p
    else fieldSub p y₂ y₁ * inverse p (fieldSub p x₂ x₁) % p
    let x₃ := fieldSub p (fieldSub p (slope * slope) x₁) x₂
    let y₃ := fieldSub p (slope * fieldSub p x₁ x₃) y₁
    .affine x₃ y₃

/--
Compute `scalar * point` by double-and-add, with zero giving the identity (SEC 1 v2.0, §2.2.1).
-/
def scalarMul (domain : Domain) (scalar : Nat) (point : Point) : Point := Id.run do
  let mut result := Point.infinity
  for i in [:scalar.log2 + 1] do
    result := add domain result result
    if scalar.testBit (scalar.log2 - i) then result := add domain result point
  return result

/--
Negation: the identity is its own negative, and the negative of `(x, y)` is `(x, −y mod p)`
(SEC 1 v2.0, §2.2.1).
-/
def neg (domain : Domain) : Point → Point
  | .infinity => .infinity
  | .affine x y => .affine x (fieldSub domain.p 0 y)

end Standards.SECG.ECC.Curve
