import Standards.SECG.DomainParameters.Secp256k1

namespace K256.Proofs.Generate.Curve.Group

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem generator_onCurve : Curve.onCurve domain domain.G = true := by decide +kernel

theorem generator_order : Curve.scalarMul domain domain.n domain.G = .infinity := by decide +kernel

end K256.Proofs.Generate.Curve.Group
