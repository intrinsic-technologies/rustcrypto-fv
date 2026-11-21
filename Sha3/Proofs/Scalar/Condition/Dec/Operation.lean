import X86Proofs.Core.Run
import Sha3.Proofs.Scalar.Condition.Dec.Spec

namespace X86Proofs

open X86 X86.Helpers

theorem ofInt_toNat_sub_one {n : Nat} (x : BitVec n) :
    BitVec.ofInt n ((x.toNat : Int) - 1) = x - 1 := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_natCast,
    BitVec.ofNat_toNat, BitVec.setWidth_eq, ← BitVec.sub_eq_add_neg]
  rfl

theorem dec_af_iff {n : Nat} (x : BitVec n) :
    (max (((x.toNat : Int) - 1) % 16) 0 = (x.toNat : Int) % 16 - 1) ↔
      ¬ x.extractLsb' 0 4 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.extractLsb'_toNat]
  show _ ↔ ¬ x.toNat >>> 0 % 2 ^ 4 = 0
  rw [Nat.shiftRight_zero]
  omega

theorem dec_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) :
    (X86.Instructions.Operations.DEC n x).run s =
      let (r, flags) := decSpec (StatusFlags.ofRFLAGS s.RFLAGS) x
      (.ok r, setFlags s flags) := by
  simp only [setFlags]
  rw [StatusFlags.store_of_cf_eq _ _ rfl]
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.DEC
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp only [Int.cast_ofNat_Int, Int.reduceToNat, unsigned_eq, BitVec.ofNat_eq_ofNat,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Int.toNat_one, Nat.pow_one,
      Nat.mod_succ, Int.zero_add, Int.toNat_zero, Int.pow_zero, Int.ediv_one,
      ofInt_toNat_sub_one, signed_eq, BitVec.toInt_zero, beq_iff_eq, Int.reduceSub,
      Nat.reduceAdd, extractLsb'_msb, beq_zero_eq_decide, decide_eq_true_eq, Int.reduceAdd,
      BitVec.toNat_ofInt, Int.ofNat_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      Int.natCast_emod, BitVec.extractLsb'_zero, dec_af_iff, ite_not,
      BitVec.extractLsb'_eq_self, specM_pure_run, decSpec, ne_eq, decide_not]
    repeat rw [ite_zero_one]
    repeat rw [ite_one_zero]
    simp

end X86Proofs
