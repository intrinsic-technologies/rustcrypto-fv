import AesGcm.Proofs.AES16.KeySchedule.Algebra
namespace AesGcm.Proofs.Machine.AES16.KeySchedule
open X86 X86.Machine

def adjustDelta32 (x : BitVec 32) (shift : Nat) (mask : BitVec 32) : BitVec 32 :=
  let t := ((x >>> shift) ^^^ x) &&& mask
  (t <<< shift) ^^^ (x ^^^ t)

private theorem and_setWidth16 (x : BitVec 32) (m : BitVec 16) :
    x &&& m.setWidth 32 = ((x.setWidth 16) &&& m).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 16
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, hi, h,
      decide_true, Bool.true_and]
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, hi, h,
      decide_true, decide_false, Bool.false_and, Bool.and_false,
      BitVec.getLsbD_of_ge m i (by omega)]

private theorem masked_shift_setWidth16 (x m : BitVec 16) (s : Nat)
    (h : m.setWidth 32 <<< s = (m <<< s).setWidth 32) :
    ((x &&& m).setWidth 32) <<< s = ((x &&& m) <<< s).setWidth 32 := by
  rw [BitVec.setWidth_and, BitVec.shiftLeft_and_distrib, h, and_setWidth16]
  simp only [BitVec.setWidth_shiftLeft_of_le (show 16 ≤ 32 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 16 ≤ 32 by decide), BitVec.setWidth_eq]
  rw [← BitVec.shiftLeft_and_distrib]

theorem adjustDelta32_u16 (x m : BitVec 16) (s : Nat)
    (h : m.setWidth 32 <<< s = (m <<< s).setWidth 32) :
    adjustDelta32 (x.setWidth 32) s (m.setWidth 32) =
      (AES16.deltaSwap1 x s m).setWidth 32 := by
  have ht : ((x.setWidth 32 >>> s) ^^^ x.setWidth 32) &&& m.setWidth 32 =
      (((x >>> s) ^^^ x) &&& m).setWidth 32 := by
    rw [← BitVec.setWidth_ushiftRight (show 16 ≤ 32 by decide)]
    rw [← BitVec.setWidth_xor, ← BitVec.setWidth_and]
  simp only [adjustDelta32, ht, masked_shift_setWidth16 _ _ _ h,
    ← BitVec.setWidth_xor, AES16.deltaSwap1]
  congr 1
  rw [BitVec.xor_comm (x >>> s) x]
  ac_rfl

theorem adjustDelta32_1320 (x : BitVec 16) :
    adjustDelta32 (x.setWidth 32) 2 0x1320 =
      (AES16.deltaSwap1 x 2 0x1320).setWidth 32 :=
  adjustDelta32_u16 x 0x1320 2 (by decide +kernel)

theorem adjustDelta32_2310 (x : BitVec 16) :
    adjustDelta32 (x.setWidth 32) 2 0x2310 =
      (AES16.deltaSwap1 x 2 0x2310).setWidth 32 :=
  adjustDelta32_u16 x 0x2310 2 (by decide +kernel)

theorem adjustDelta32_3030 (x : BitVec 16) :
    adjustDelta32 (x.setWidth 32) 2 0x3030 =
      (AES16.deltaSwap1 x 2 0x3030).setWidth 32 :=
  adjustDelta32_u16 x 0x3030 2 (by decide +kernel)

theorem adjustDelta32_5050 (x : BitVec 16) :
    adjustDelta32 (x.setWidth 32) 1 0x5050 =
      (AES16.deltaSwap1 x 1 0x5050).setWidth 32 :=
  adjustDelta32_u16 x 0x5050 1 (by decide +kernel)

theorem adjust_deltaSwap_machine (x mask : BitVec 32) (shift : Nat) :
    (((x >>> shift ^^^ x) &&& mask) <<< shift) ^^^
      (x ^^^ ((x >>> shift ^^^ x) &&& mask)) = adjustDelta32 x shift mask := rfl

theorem adjust_add_self {w : Nat} (x : BitVec w) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_two]

end AesGcm.Proofs.Machine.AES16.KeySchedule
