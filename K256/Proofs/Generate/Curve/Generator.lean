import K256.Proofs.Generate.Curve.Group.Laws
import K256.Proofs.Generate.Curve.Group.Scalar
import K256.Proofs.Generate.Curve.Group.Order

namespace K256.Proofs.Generate.Curve

open Standards.SECG.ECC
open Standards.SECG.DomainParameters.Secp256k1

open Group

def generatorMultiple (k : Int) : Curve.Point :=
  Curve.scalarMul domain (k % (domain.n : Int)).toNat domain.G

theorem generatorMultiple_add (k l : Int) :
    Curve.add domain (generatorMultiple k) (generatorMultiple l) = generatorMultiple (k + l) := by
  have hmul := multiple_add domain secp256k1_add_laws domain.G generator_onCurve
  have hrep := scalarMul_eq_multiple domain secp256k1_add_laws domain.G generator_onCurve
  have horder : multiple domain domain.G domain.n = .infinity :=
    (hrep domain.n).symm.trans generator_order
  have hperiod (i : Nat) : multiple domain domain.G (domain.n + i) = multiple domain domain.G i := by
    rw [hmul, horder]
    rfl
  have hn : 0 < domain.n := by decide +kernel
  have hn' : (0 : Int) < domain.n := by omega
  have hk := Int.emod_nonneg k (Int.ne_of_gt hn')
  have hl := Int.emod_nonneg l (Int.ne_of_gt hn')
  simp only [generatorMultiple, hrep, ← hmul]
  rw [Int.add_emod k l, Int.toNat_emod (Int.add_nonneg hk hl) (Int.le_of_lt hn'), Int.toNat_add hk hl]
  exact periodic_eq_mod _ _ hn hperiod _

theorem generatorMultiple_onCurve (k : Int) : Curve.onCurve domain (generatorMultiple k) = true := by
  rw [generatorMultiple, scalarMul_eq_multiple domain secp256k1_add_laws domain.G generator_onCurve]
  exact multiple_onCurve domain secp256k1_add_laws domain.G generator_onCurve _

theorem generatorMultiple_neg (k : Int) :
    Curve.neg domain (generatorMultiple k) = generatorMultiple (-k) := by
  apply neg_eq_of_add_eq_infinity _ _ (generatorMultiple_onCurve _) (generatorMultiple_onCurve _)
  rw [generatorMultiple_add, show k + -k = 0 by omega]
  decide +kernel

end K256.Proofs.Generate.Curve
