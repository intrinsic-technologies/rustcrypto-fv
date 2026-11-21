import Standards.SECG.ECC.Curve

/-!
# P-256 domain parameters

The prime field, curve coefficients, subgroup order, cofactor, and base point from NIST SP 800-186,
§3.2.1.3. The optional generation seed and its SHA-1 output `c` are omitted.

Source: https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-186.pdf
-/

set_option autoImplicit false

namespace Standards.NIST.EllipticCurves.P256

/-- P-256 domain parameters (NIST SP 800-186, §3.2.1.3) -/
def domain : Standards.SECG.ECC.Curve.Domain := {
  p := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
  a := 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc
  b := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  G := .affine
    0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
    0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
  n := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  h := 1
}

end Standards.NIST.EllipticCurves.P256
