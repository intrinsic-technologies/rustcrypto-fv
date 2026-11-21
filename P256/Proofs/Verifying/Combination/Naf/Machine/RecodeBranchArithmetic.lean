import P256.Proofs.Verifying.Combination.Naf.Arithmetic
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open X86 X86.Machine X86.Helpers X86Proofs
open P256.Proofs.Common.Instructions.ByteOps.ByteOps (mergeGPR_low8)

theorem window_ult_sixteen {w : Nat} (bound : w ≤ 32) :
    (BitVec.ofNat 64 w).ult 16#64 = decide (w < 16) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : w < 2^64)]

theorem window_carry_merge (w : Nat) :
    mergeGPR 8 (if decide (w<16) then 0 else 1) 0 = BitVec.ofNat 64 (carry w) := by
  by_cases small : w<16 <;> simp [small, carry, mergeGPR, X86.Runtime.setSlice]

theorem window_digit_byte {w : Nat} (bound : w ≤ 32) :
    (BitVec.ofNat 64 w).setWidth 8 -
      (if decide (w<16) then (0 : BitVec 32) else 32).setWidth 8 = BitVec.ofInt 8 (digit w) := by
  rw [BitVec.setWidth_ofNat_of_le (by decide)]
  by_cases small : w<16
  · simp [small, digit, carry]
  · simp only [small, decide_false, Bool.false_eq_true, ite_false, digit, carry,
      Int.natCast_one, Int.mul_one]
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 8 w - 32#8).toNat = (BitVec.ofInt 8 ((w : Int)-32)).toNat
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofInt,
      Nat.mod_eq_of_lt (by omega : w < 256), Nat.reducePow, Nat.reduceMod]
    omega

theorem window_digit_merge {w : Nat} (bound : w ≤ 32) (old : BitVec 64) :
    (mergeGPR 8 ((BitVec.ofNat 64 w).setWidth 8 -
      (if decide (w<16) then (0 : BitVec 32) else 32).setWidth 8) old).setWidth 8 =
        BitVec.ofInt 8 (digit w) := by
  rw [mergeGPR_low8, window_digit_byte bound]

theorem remaining_bits {i w : Nat} (index : i < 256) :
    -BitVec.ofNat 64 i + 256 - BitVec.ofNat 64 (carry w) =
      BitVec.ofNat 64 (256-i-carry w) := by
  have left : -BitVec.ofNat 64 i + 256 = BitVec.ofNat 64 (256-i) := by
    rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg]
    exact BitVec.ofNat_sub_ofNat_of_le 256 i (by omega) (by omega)
  rw [left]
  have carryBound := carry_le_one w
  exact BitVec.ofNat_sub_ofNat_of_le (256-i) (carry w) (by omega) (by omega)

theorem remaining_bits_toNat {i w : Nat} (index : i < 256) :
    (-BitVec.ofNat 64 i + 256 - BitVec.ofNat 64 (carry w)).toNat = 256-i-carry w := by
  rw [remaining_bits index, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem remaining_bits_ult {i w : Nat} (index : i < 256) :
    (-BitVec.ofNat 64 i + 256 - BitVec.ofNat 64 (carry w)).ult 5#64 =
      decide (256-i-carry w < 5) := by
  rw [BitVec.ult, remaining_bits_toNat index]
  rfl

theorem remaining_skip {i w : Nat} (index : i < 256) :
    (if (-BitVec.ofNat 64 i + 256 - BitVec.ofNat 64 (carry w)).ult 5#64 then
      -BitVec.ofNat 64 i + 256 - BitVec.ofNat 64 (carry w) else 5) =
        BitVec.ofNat 64 (skip (256-i) w) := by
  rw [remaining_bits_ult index, remaining_bits index]
  by_cases small : 256-i-carry w < 5
  · have h : skip (256-i) w = 256-i-carry w := by unfold skip; omega
    simp only [small, decide_true, ite_true, h]
  · have h : skip (256-i) w = 5 := by unfold skip; omega
    simp only [small, decide_false, Bool.false_eq_true, ite_false, h]
    rfl

theorem recode_room {i : Nat} (index : i < 256) :
    257#64 - BitVec.ofNat 64 i = BitVec.ofNat 64 (257-i) :=
  BitVec.ofNat_sub_ofNat_of_le 257 i (by omega) (by omega)

end P256.Proofs.Verifying.Combination.Naf.Machine
