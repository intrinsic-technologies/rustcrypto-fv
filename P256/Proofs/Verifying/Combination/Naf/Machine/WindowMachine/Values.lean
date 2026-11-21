import P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine

open X86Proofs

theorem index_shift_count (i : Nat) :
    shiftCount 64 ((BitVec.ofNat 64 (i%64)).setWidth 8)=i%64 := by
  simp only [shiftCount,↓reduceIte,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  omega

theorem negative_shift_count {i : Nat} (cross : 64≤i%64+5) :
    shiftCount 64 ((-BitVec.ofNat 64 i).setWidth 8)=64-i%64 := by
  simp only [shiftCount,↓reduceIte,BitVec.toNat_setWidth,BitVec.toNat_neg,BitVec.toNat_ofNat]
  omega

theorem low_bit_zero (v : Nat) :
    (((BitVec.ofNat 64 v).setWidth 8 &&& 1)==0)=decide (v%2=0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq,← BitVec.toNat_inj,BitVec.toNat_and,
    BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  change ((v%2^64)%2^8 &&& (2^1-1))=0 ↔ v%2=0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

end P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine
