import Standards.SECG.ECC.Curve

/-!
# Prime-field auxiliary operations

Prime-field operations used with the curves of SP 800-186: arithmetic in GF(p) (§3.1.2 and
Appendix E.4), which reduces its inputs modulo `p`, and the `p ≡ 3 mod 4` case of the square roots
of Appendix E.3. Subtraction and inversion are those of the SEC 1 definitions, `Curve.fieldSub` and
`Curve.inverse`. Inversion and the square roots state the primes they are valid for.

Source: https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-186.pdf
-/

set_option autoImplicit false

namespace Standards.NIST.EllipticCurves.Field

/--
Return `value^((p+1)/4) mod p`, whichever of the two roots it is, when it squares to `value` modulo
a prime `p ≡ 3 mod 4`, else `none` (SP 800-186, Appendix E.3). Not a general prime-field root.
-/
def sqrtMod3Mod4 (p value : Nat) : Option Nat :=
  let root := Standards.SECG.ECC.Curve.powMod p value ((p + 1) / 4)
  if root * root % p == value % p then some root else none

/-- Sum of two elements of GF(p), computed modulo `p` (SP 800-186, §3.1.2) -/
def add (p x y : Nat) : Nat := (x + y) % p

/-- Difference of two elements of GF(p), computed modulo `p` (SP 800-186, §3.1.2) -/
def sub (p x y : Nat) : Nat := Standards.SECG.ECC.Curve.fieldSub p x y

/-- Additive inverse of an element of GF(p), computed modulo `p` (SP 800-186, §3.1.2) -/
def neg (p x : Nat) : Nat := sub p 0 x

/-- Product of two elements of GF(p), computed modulo `p` (SP 800-186, §3.1.2) -/
def mul (p x y : Nat) : Nat := x * y % p

/--
Multiplicative inverse `x^(p−2)` of an element of GF(p) for prime `p`, or `none` for zero, which
has no inverse (SP 800-186, Appendix E.4)
-/
def inverse (p x : Nat) : Option Nat :=
  if x % p = 0 then none else some (Standards.SECG.ECC.Curve.inverse p x)

end Standards.NIST.EllipticCurves.Field
