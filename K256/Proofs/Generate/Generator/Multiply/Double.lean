import K256.Proofs.Generate.Generator.Multiply.Add

namespace K256.Proofs.Generate.Generator.Multiply.Projective

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem double_correct (p : Projective) (hp : p.valid) :
    (p.double).valid ∧ (p.double).value = Curve.add domain p.value p.value := by
  have hdouble : p.double = p.add p := by
    have hcurve := hp.1
    cases p
    congr 1 <;> dsimp only [double, add] <;> grind only
  rw [hdouble]
  exact add_correct p p hp hp

end K256.Proofs.Generate.Generator.Multiply.Projective
