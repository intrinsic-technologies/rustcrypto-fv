import P256.Proofs.Field.Subtract.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift

class Parameters where
  modulus : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs
  inverse : BitVec 64
  positive : 0 < modulus.toNat
  inverse_spec : ((modulus.toNat : Int) * inverse.toNat) % (2 : Int)^64 = 1

variable [parameters : Parameters]

theorem modulus_bound : parameters.modulus.toNat < 2^256 :=
  P256.Proofs.SecretKeyFromBytes.Scalar.limbs_toNat_lt _

theorem inverse_mod_two_pow {shift : Nat} (bound : shift ≤ 64) :
    ((parameters.modulus.toNat : Int) * parameters.inverse.toNat) % (2 : Int)^shift =
      1 % (2 : Int)^shift := by
  have divisible : (2 : Int)^shift ∣ (2 : Int)^64 := by
    exact_mod_cast Nat.pow_dvd_pow 2 bound
  rw [← Int.emod_emod_of_dvd _ divisible, parameters.inverse_spec]

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift
