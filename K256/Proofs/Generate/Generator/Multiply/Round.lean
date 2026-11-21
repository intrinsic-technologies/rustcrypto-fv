import K256.Proofs.Generate.Generator.Multiply.Add
import K256.Proofs.Generate.Generator.Multiply.Double
import K256.Proofs.Generate.Curve.Window

namespace K256.Proofs.Generate.Generator.Multiply.Projective

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

def round (acc left right : Projective) : Projective :=
  (acc.double.double.double.double.add left).add right

theorem round_correct (acc left right : Projective)
    (ha : acc.valid) (hl : left.valid) (hr : right.valid) :
    (round acc left right).valid ∧ (round acc left right).value =
      Curve.add domain (Curve.add domain (Generate.Curve.fourDoubles acc.value) left.value)
        right.value := by
  obtain ⟨h₁, v₁⟩ := double_correct _ ha
  obtain ⟨h₂, v₂⟩ := double_correct _ h₁
  obtain ⟨h₃, v₃⟩ := double_correct _ h₂
  obtain ⟨h₄, v₄⟩ := double_correct _ h₃
  obtain ⟨h₅, v₅⟩ := add_correct _ _ h₄ hl
  obtain ⟨h₆, v₆⟩ := add_correct _ _ h₅ hr
  exact ⟨h₆, by simpa only [round, v₅, v₄, v₃, v₂, v₁, Generate.Curve.fourDoubles] using v₆⟩

end K256.Proofs.Generate.Generator.Multiply.Projective
