import Standards.SECG.DomainParameters.Secp256k1
import Standards.SECG.ECC.Points
import Standards.NIST.EllipticCurves.Field
import Standards.Tests.Utilities

/-!
# SEC 2 tests

secp256k1 domain parameters against the values printed in SEC 2 v2.0, §2.4.1.

| Source   | Vectors       | Checks                                                       |
| -------- | ------------- | ------------------------------------------------------------ |
| §2.4.1   | secp256k1 `G` | `p` formula, both encodings of `G`, `G` on the curve, `nG = O` |
-/

namespace Standards.SECG.DomainParameters.Tests

open Standards.Tests Standards.SECG.ECC Standards.SECG.DomainParameters

def run : IO Unit := do
  let domain := Secp256k1.domain
  let sqrtMod := Standards.NIST.EllipticCurves.Field.sqrtMod3Mod4 domain.p
  check "secp256k1 p" (domain.p == 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1)
  let compressed ← hex "02 79BE667E F9DCBBAC 55A06295 CE870B07 029BFCDB 2DCE28D9 59F2815B 16F81798"
  let uncompressed ← hex ("04 79BE667E F9DCBBAC 55A06295 CE870B07 029BFCDB 2DCE28D9 59F2815B" ++
    "16F81798 483ADA77 26A3C465 5DA4FBFC 0E1108A8 FD17B448 A6855419 9C47D08F FB10D4B8")
  expect "secp256k1 compressed G" (Points.encodePoint domain true domain.G) compressed
  expect "secp256k1 uncompressed G" (Points.encodePoint domain false domain.G) uncompressed
  check "secp256k1 compressed G decodes"
    (Points.decodePoint domain sqrtMod compressed == some domain.G)
  check "secp256k1 G lies on the curve" (Curve.onCurve domain domain.G)
  check "secp256k1 nG = O" (Curve.scalarMul domain domain.n domain.G == .infinity)
  check "secp256k1 (n - 1)G = -G"
    (Curve.scalarMul domain (domain.n - 1) domain.G == Curve.neg domain domain.G)
  IO.println "SEC 2: secp256k1 domain parameter checks passed"

end Standards.SECG.DomainParameters.Tests
