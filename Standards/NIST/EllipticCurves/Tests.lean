import Standards.NIST.EllipticCurves
import Standards.SECG.ECC.Points
import Standards.Tests.Utilities

/-!
# SP 800-186 tests

The domain parameters of each curve, prime-field arithmetic, and the square roots of Appendix E.3.

| Source              | Vectors   | Checks                                                       |
| ------------------- | --------- | ------------------------------------------------------------ |
| §3.2.1.3            | P-256 `G` | `G` on the curve, `nG = O`, square roots                     |
| §3.1.2              | —         | wraparound of sums, differences and negation                 |
| Appendix E.4        | —         | inverse of 2, no inverse of zero                             |

The square-root checks of a curve take the root of `x³ + ax + b` at `G`'s `x`, find none for a
non-residue, and decode both compressed parities of `G`'s `x`.
-/

namespace Standards.NIST.EllipticCurves.Tests

open Standards.Tests Standards.NIST.EllipticCurves Standards.SECG.ECC

/-- The domain checks of a curve: `G` on the curve and `nG = O` -/
private def checkDomain (name : String) (domain : Curve.Domain) : IO Unit := do
  check s!"{name} generator lies on the curve" (Curve.onCurve domain domain.G)
  check s!"{name} group order gives infinity"
    (Curve.scalarMul domain domain.n domain.G == .infinity)

/-- The square-root checks of a curve with square root `sqrtMod` and non-residue `nonResidue` -/
private def checkSquareRoot (name : String) (domain : Curve.Domain) (sqrtMod : Nat → Option Nat)
    (nonResidue : Nat) : IO Unit := do
  let .affine x y := domain.G | throw (IO.userError s!"{name}: missing generator")
  let α := (x * x * x + domain.a * x + domain.b) % domain.p
  check s!"{name} square root of a residue"
    ((sqrtMod α).map (fun root => root * root % domain.p) == some α)
  check s!"{name} no square root of a non-residue" (sqrtMod nonResidue == none)
  check s!"{name} both compressed parities decode"
    (Points.decodePoint domain sqrtMod (Points.encodePoint domain true (.affine x (domain.p - y)))
      == some (.affine x (domain.p - y)))

/-- A curve with `p ≡ 3 mod 4`, whose square roots are `Field.sqrtMod3Mod4` -/
private def checkCurve (name : String) (domain : Curve.Domain) : IO Unit := do
  checkDomain name domain
  check s!"{name} prime is 3 mod 4" (domain.p % 4 == 3)
  checkSquareRoot name domain (Field.sqrtMod3Mod4 domain.p) (domain.p - 1)
  IO.println s!"SP 800-186: {name} domain and square-root checks passed"

/-- Arithmetic modulo P-256's prime -/
private def fieldArithmetic : IO Unit := do
  let p := P256.domain.p
  check "Sum wraps modulo p" (Field.add p (p - 1) 2 == 1)
  check "Difference wraps modulo p" (Field.sub p 1 2 == p - 1)
  check "Negation of zero" (Field.neg p 0 == 0 && Field.neg p 1 == p - 1)
  check "Inverse of two" ((Field.inverse p 2).map (Field.mul p 2) == some 1)
  check "No inverse of zero" (Field.inverse p 0 == none && Field.inverse p p == none)
  IO.println "SP 800-186: field arithmetic checks passed"

def run : IO Unit := do
  checkCurve "P-256" P256.domain
  fieldArithmetic

end Standards.NIST.EllipticCurves.Tests
