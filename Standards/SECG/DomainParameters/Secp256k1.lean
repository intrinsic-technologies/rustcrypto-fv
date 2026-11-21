import Standards.SECG.ECC.Curve

/-!
# secp256k1 domain parameters

The prime field, curve coefficients, base point, subgroup order, and cofactor of the Koblitz curve
secp256k1 from SEC 2 v2.0, §2.4.1.

Source: https://www.secg.org/sec2-v2.pdf
-/

set_option autoImplicit false

namespace Standards.SECG.DomainParameters.Secp256k1

/-- secp256k1 domain parameters `(p, a, b, G, n, h)` (SEC 2 v2.0, §2.4.1) -/
def domain : Standards.SECG.ECC.Curve.Domain := {
  p := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
  a := 0
  b := 7
  G := .affine
    0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
    0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
  n := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
  h := 1
}

end Standards.SECG.DomainParameters.Secp256k1
