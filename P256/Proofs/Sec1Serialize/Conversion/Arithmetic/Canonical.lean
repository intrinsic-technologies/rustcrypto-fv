import P256.Proofs.Sec1Serialize.Conversion.Arithmetic.Montgomery
import P256.Proofs.Sec1Serialize.State
import P256.Proofs.Common.Instructions.Mul.Spec

set_option autoImplicit false

open P256.Proofs.Sec1Serialize.Conversion.Montgomery (compilerRoundBV limbsToNat limbsToNat_digits_eq p reduceFour reduceStep reduceStep_add_wordMultiple reduceStep_lt wordBase)
open P256.Proofs.Common.Instructions (mulHigh64)

namespace P256.Proofs.Sec1Serialize.Conversion

open X86Proofs

theorem canonicalLimbs_of_limbsToNat {a0 a1 a2 a3 : BitVec 64} {x : Nat}
    (h : limbsToNat a0.toNat a1.toNat a2.toNat a3.toNat = x) :
    a0 = canonicalLimb x 0 ∧ a1 = canonicalLimb x 1 ∧
      a2 = canonicalLimb x 2 ∧ a3 = canonicalLimb x 3 := by
  have hd := limbsToNat_digits_eq _ _ _ _ a0.isLt a1.isLt a2.isLt a3.isLt
  dsimp only at hd
  rw [h] at hd
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · simpa only [canonicalLimb, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
      BitVec.toNat_ofNat] using hd.1.symm
  · simpa only [canonicalLimb, Nat.mul_one, BitVec.toNat_ofNat] using hd.2.1.symm
  · simpa only [canonicalLimb, wordBase, Nat.reduceMul, Nat.reducePow,
      BitVec.toNat_ofNat] using hd.2.2.1.symm
  · simpa only [canonicalLimb, wordBase, Nat.reduceMul, Nat.reducePow,
      BitVec.toNat_ofNat] using hd.2.2.2.symm

theorem reduceStep_limbs_delayed (a0 a1 a2 a3 : Nat) :
    reduceStep (limbsToNat a0 a1 a2 a3) =
      (reduceStep a0 + a1) + wordBase * (a2 + wordBase * a3) := by
  rw [limbsToNat, reduceStep_add_wordMultiple]
  omega

theorem reduceStep_two_delayed (a0 a1 a2 a3 : Nat) :
    reduceStep (reduceStep (limbsToNat a0 a1 a2 a3)) =
      (reduceStep (reduceStep a0 + a1) + a2) + wordBase * a3 := by
  rw [reduceStep_limbs_delayed, reduceStep_add_wordMultiple]
  omega

theorem reduceStep_three_delayed (a0 a1 a2 a3 : Nat) :
    reduceStep (reduceStep (reduceStep (limbsToNat a0 a1 a2 a3))) =
      reduceStep (reduceStep (reduceStep a0 + a1) + a2) + a3 := by
  rw [reduceStep_two_delayed, reduceStep_add_wordMultiple]

theorem reduceFour_delayed (a0 a1 a2 a3 : Nat) :
    reduceFour (limbsToNat a0 a1 a2 a3) =
      reduceStep (reduceStep (reduceStep (reduceStep a0 + a1) + a2) + a3) := by
  unfold reduceFour
  rw [reduceStep_three_delayed]

theorem reduceStep_delayed_bounds {a0 a1 a2 a3 : Nat}
    (h : limbsToNat a0 a1 a2 a3 < p) :
    reduceStep a0 + a1 < p ∧
      reduceStep (reduceStep a0 + a1) + a2 < p ∧
      reduceStep (reduceStep (reduceStep a0 + a1) + a2) + a3 < p := by
  have h1 := reduceStep_lt _ h
  have h2 := reduceStep_lt _ h1
  have h3 := reduceStep_lt _ h2
  rw [reduceStep_limbs_delayed] at h1
  rw [reduceStep_two_delayed] at h2
  rw [reduceStep_three_delayed] at h3
  exact ⟨Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h1,
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h2, h3⟩

theorem limbsToNat_canonicalLimb (x : Nat) (hx : x < 2^256) :
    limbsToNat (canonicalLimb x 0).toNat (canonicalLimb x 1).toNat
      (canonicalLimb x 2).toNat (canonicalLimb x 3).toNat = x := by
  simp only [canonicalLimb, limbsToNat, wordBase, BitVec.toNat_ofNat,
    Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one, Nat.reduceMul, Nat.reducePow]
  omega

def compilerConversionBV (a0 a1 a2 a3 : BitVec 64) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let r1 := compilerRoundBV (a0 <<< 32) (a0 >>> 32)
    (a0 * 0xffffffff00000001) (mulHigh64 a0 0xffffffff00000001) a1
  let r2 := compilerRoundBV r1.1 r1.2.1 r1.2.2.1 r1.2.2.2 a2
  compilerRoundBV r2.1 r2.2.1 r2.2.2.1 r2.2.2.2 a3

end P256.Proofs.Sec1Serialize.Conversion
