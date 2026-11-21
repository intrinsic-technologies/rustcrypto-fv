import K256.Proofs.Generate.Curve

namespace K256.Proofs.Ecdh.Curve

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Generate.Curve

theorem scalarMul_generatorMultiple (a : Int) (k : Nat) :
    Curve.scalarMul domain k (generatorMultiple a) = generatorMultiple ((k : Int) * a) := by
  rw [Group.scalarMul_eq_multiple domain Group.secp256k1_add_laws _ (generatorMultiple_onCurve a)]
  induction k with
  | zero => simp only [Group.multiple, Int.natCast_zero, Int.zero_mul]; decide +kernel
  | succ k ih =>
    simp only [Group.multiple, ih, generatorMultiple_add, Int.natCast_succ, Int.add_mul, Int.one_mul]

end K256.Proofs.Ecdh.Curve
