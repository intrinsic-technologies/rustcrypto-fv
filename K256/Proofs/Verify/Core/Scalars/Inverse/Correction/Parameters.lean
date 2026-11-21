import K256.Proofs.Common.Invert.ModularShift.Wide
import Standards.SECG.DomainParameters.Secp256k1

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Correction

open Common.Invert.ModularShift (limbs)
open Generate.Generator.Affine.Invert.SafeGcd (shift_mask)

structure Parameters where
  modulusWords : Vector (BitVec 64) 4
  negativeInverse : BitVec 64
  positive : 0 < (limbs modulusWords).toNat
  inverse : BitVec.ofNat 64 (limbs modulusWords).toNat * negativeInverse = -1

def Parameters.inverseWord (p : Parameters) : BitVec 64 := -p.negativeInverse

theorem Parameters.inverse_mod_two_pow (p : Parameters) {shift : Nat} (bound : shift ≤ 64) :
    (((limbs p.modulusWords).toNat : Int) * p.inverseWord.toNat) % (2 : Int)^shift =
      1 % (2 : Int)^shift := by
  have word : BitVec.ofNat 64 (limbs p.modulusWords).toNat * p.inverseWord = 1 := by
    rw [Parameters.inverseWord, BitVec.mul_neg, p.inverse]
    rfl
  have h := congrArg BitVec.toNat word
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mul_mod] at h
  have full : (((limbs p.modulusWords).toNat : Int) * p.inverseWord.toNat) % (2 : Int)^64 = 1 := by
    exact_mod_cast h
  have divides : (2 : Int)^shift ∣ (2 : Int)^64 := by exact_mod_cast Nat.pow_dvd_pow 2 bound
  rw [← Int.emod_emod_of_dvd _ divides, full]

def orderParameters : Parameters where
  modulusWords := #v[0xbfd25e8cd0364141, 0xbaaedce6af48a03b, 0xfffffffffffffffe, 0xffffffffffffffff]
  negativeInverse := -0xb4f20099aa774ec1
  positive := by decide +kernel
  inverse := by decide +kernel

theorem order_modulus : (limbs orderParameters.modulusWords).toNat =
    Standards.SECG.DomainParameters.Secp256k1.domain.n := by decide +kernel

theorem order_inverseWord : orderParameters.inverseWord = 0xb4f20099aa774ec1 := by decide +kernel

def Parameters.correctionWord (p : Parameters) (magnitude : Nat) (shift : Nat) : BitVec 64 :=
  ((p.inverseWord * BitVec.ofNat 64 magnitude) <<< (64-shift)) >>> (64-shift)

theorem Parameters.correctionWord_eq (p : Parameters) (magnitude shift : Nat) (hs : shift ≤ 64) :
    p.correctionWord magnitude shift =
      (BitVec.ofNat shift (magnitude * p.inverseWord.toNat)).setWidth 64 := by
  rw [Parameters.correctionWord, shift_mask _ hs]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mul_mod_mod, Nat.mul_comm p.inverseWord.toNat magnitude,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hs)]

theorem Parameters.correctionWord_value (p : Parameters) (magnitude shift : Nat) (hs : shift ≤ 64) :
    ((p.correctionWord magnitude shift).toNat : Int) =
      ((magnitude : Int) * p.inverseWord.toNat) % (2 : Int)^shift := by
  rw [p.correctionWord_eq magnitude shift hs, BitVec.toNat_setWidth]
  have hn : (BitVec.ofNat shift (magnitude * p.inverseWord.toNat)).toNat < 2^64 :=
    Nat.lt_of_lt_of_le (BitVec.isLt _) (Nat.pow_le_pow_right (by decide) hs)
  rw [Nat.mod_eq_of_lt hn, BitVec.toNat_ofNat]
  simp only [Int.natCast_emod, Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]

end K256.Proofs.Verify.Core.Scalars.Inverse.Correction
