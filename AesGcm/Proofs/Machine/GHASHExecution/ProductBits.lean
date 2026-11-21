import AesGcm.Proofs.Machine.GHASHExecution.BitOperations
import AesGcm.Proofs.Machine.GHASH.Carryless

namespace AesGcm.Proofs.Machine.GHASHExecution
open AesGcm.Proofs.Machine.GHASH

theorem mask_zero_shiftLeft (x m : BitVec 64) (n : Nat) (h : m <<< n = 0#64) :
    (x &&& m) <<< n = 0#64 := by
  rw [BitVec.shiftLeft_and_distrib, h, BitVec.and_zero]

theorem mask4444_shift62 (x : BitVec 64) :
    (x &&& 0x4444444444444444#64) <<< (62 : Nat) = 0#64 :=
  mask_zero_shiftLeft x _ _ (by decide +kernel)

theorem mask8888_shift62 (x : BitVec 64) :
    (x &&& 0x8888888888888888#64) <<< (62 : Nat) = 0#64 :=
  mask_zero_shiftLeft x _ _ (by decide +kernel)

theorem mask2222_shift63 (x : BitVec 64) :
    (x &&& 0x2222222222222222#64) <<< (63 : Nat) = 0#64 :=
  mask_zero_shiftLeft x _ _ (by decide +kernel)

theorem mask4444_shift63 (x : BitVec 64) :
    (x &&& 0x4444444444444444#64) <<< (63 : Nat) = 0#64 :=
  mask_zero_shiftLeft x _ _ (by decide +kernel)

theorem mask8888_shift63 (x : BitVec 64) :
    (x &&& 0x8888888888888888#64) <<< (63 : Nat) = 0#64 :=
  mask_zero_shiftLeft x _ _ (by decide +kernel)

theorem mul_shiftLeft_factor (x y : BitVec 64) (n : Nat) :
    (x * y) <<< n = (x <<< n) * y := by
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  ac_rfl

theorem mul_shiftLeft_factor_right (x y : BitVec 64) (n : Nat) :
    (x * y) <<< n = x * (y <<< n) := by
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  ac_rfl

theorem mask1111_mul_shift63 (x y : BitVec 64) :
    ((x &&& 0x1111111111111111#64) * (y &&& 0x1111111111111111#64)) <<< (63 : Nat) =
      (x * y) <<< (63 : Nat) := by
  rw [mul_shiftLeft_factor, mask1111_shift63]
  calc
    _ = x * ((y &&& 0x1111111111111111#64) <<< (63 : Nat)) := by
      simp only [BitVec.shiftLeft_eq_mul_twoPow]
      ac_rfl
    _ = x * (y <<< (63 : Nat)) := by rw [mask1111_shift63]
    _ = _ := (mul_shiftLeft_factor_right x y 63).symm

theorem maskedMul64_shift63 (x y : BitVec 64) :
    maskedMul64 x y <<< (63 : Nat) = (x * y) <<< (63 : Nat) := by
  simp only [maskedMul64, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_or_distrib,
    mask1111_shift63, mask2222_shift63, mask4444_shift63, mask8888_shift63,
    BitVec.or_zero, BitVec.shiftLeft_xor_distrib]
  rw [mask1111_mul_shift63]
  simp only [mul_shiftLeft_factor, mask2222_shift63, mask4444_shift63, mask8888_shift63,
    BitVec.zero_mul, BitVec.xor_zero]

attribute [local irreducible] BitVec.mul BitVec.and BitVec.or BitVec.xor BitVec.shiftLeft

theorem maskedMul64_machine_lowTwo_shift (x y : BitVec 64) :
    (((((y &&& 0x8888888888888888#64) * (x &&& 0x4444444444444444#64) ^^^
        (y &&& 0x4444444444444444#64) * (x &&& 0x8888888888888888#64)) ^^^
      ((y &&& 0x2222222222222222#64) * (x &&& 0x1111111111111111#64) ^^^
        (y &&& 0x1111111111111111#64) * (x &&& 0x2222222222222222#64))) &&&
      0x2222222222222222#64) |||
    ((((y &&& 0x2222222222222222#64) * (x &&& 0x8888888888888888#64) ^^^
        (y &&& 0x1111111111111111#64) * (x &&& 0x1111111111111111#64)) ^^^
      ((y &&& 0x8888888888888888#64) * (x &&& 0x2222222222222222#64) ^^^
        (y &&& 0x4444444444444444#64) * (x &&& 0x4444444444444444#64))) &&&
      0x1111111111111111#64)) <<< (62 : Nat) = maskedMul64 x y <<< (62 : Nat) := by
  unfold maskedMul64
  dsimp only
  simp only [BitVec.ofNat_eq_ofNat]
  simp only [BitVec.shiftLeft_or_distrib]
  simp only [mask4444_shift62, mask8888_shift62, BitVec.or_zero]
  ac_rfl

theorem maskedMul64_machine_bit0_shift (x y : BitVec 64) :
    ((y &&& 0x1111111111111111#64) * (x &&& 0x1111111111111111#64)) <<< (63 : Nat) =
      maskedMul64 x y <<< (63 : Nat) := by
  rw [mask1111_mul_shift63, maskedMul64_shift63, BitVec.mul_comm]


end AesGcm.Proofs.Machine.GHASHExecution
