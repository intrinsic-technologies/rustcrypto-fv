import AesGcm.Proofs.Machine.GHASH.BitReverse
import X86Proofs.Instructions.Bswap.Operation

namespace AesGcm.Proofs.Machine.GHASHExecution

open X86Proofs AesGcm.Proofs.Machine.GHASH

theorem mul_two_shift (x : BitVec 64) : x * 2 = x <<< (1 : Nat) :=
  BitVec.mul_twoPow_eq_shiftLeft x 1

theorem mul_four_shift (x : BitVec 64) : x * 4 = x <<< (2 : Nat) :=
  BitVec.mul_twoPow_eq_shiftLeft x 2

theorem mask_shiftLeft_eq (x m : BitVec 64) (n : Nat)
    (h : m <<< n = (BitVec.allOnes 64) <<< n) :
    (x &&& m) <<< n = x <<< n := by
  rw [BitVec.shiftLeft_and_distrib, h, ← BitVec.shiftLeft_and_distrib,
    BitVec.and_allOnes]

theorem mask3333_shift62 (x : BitVec 64) :
    (x &&& 0x3333333333333333#64) <<< (62 : Nat) = x <<< (62 : Nat) :=
  mask_shiftLeft_eq x _ _ (by decide +kernel)

theorem mask1111_shift63 (x : BitVec 64) :
    (x &&& 0x1111111111111111#64) <<< (63 : Nat) = x <<< (63 : Nat) :=
  mask_shiftLeft_eq x _ _ (by decide +kernel)

theorem bswapSpec_eq_swapBytes64 (x : BitVec 64) : bswapSpec x = swapBytes64 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bswapSpec, getLsbD_ofLanes _ i hi]
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
      i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
      i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨
      i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨
      i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨
      i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨
      i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [lane, swapBytes64,
      BitVec.getLsbD_append, BitVec.getLsbD_extractLsb'] <;> simp

theorem reverseBits64_machine (x : BitVec 64) :
    let a : BitVec 64 := bswapSpec x
    let b : BitVec 64 := ((a &&& 0x0f0f0f0f0f0f0f0f#64) <<< (4 : Nat)) |||
      ((a >>> (4 : Nat)) &&& 0x0f0f0f0f0f0f0f0f#64)
    let c : BitVec 64 := ((b >>> (2 : Nat)) &&& 0x3333333333333333#64) +
      ((b &&& 0x3333333333333333#64) <<< (2 : Nat))
    ((c >>> (1 : Nat)) &&& 0x5555555555555555#64) +
      ((c &&& 0x5555555555555555#64) <<< (1 : Nat)) = x.reverse := by
  simpa only [reverseBits64, bswapSpec_eq_swapBytes64, BitVec.or_comm] using
    reverseBits64_eq_reverse x


theorem reverseLast_clear (x : BitVec 64) :
    ((x >>> (1 : Nat)) &&& 0x5555555555555554#64) +
      ((x &&& 0x5555555555555555#64) <<< (1 : Nat)) =
    ((((x >>> (1 : Nat)) &&& 0x5555555555555555#64) +
      ((x &&& 0x5555555555555555#64) <<< (1 : Nat))) >>> (1 : Nat)) <<< (1 : Nat) := by
  rw [maskedSwap_add_eq_or _ _ _ (by decide +kernel)]
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · rw [BitVec.shiftLeft_ushiftRight, BitVec.and_or_distrib_right]
    congr 1
    · rw [BitVec.and_assoc]
      rfl
    · change _ = (x &&& 0x5555555555555555#64) <<< 1 &&&
        (BitVec.allOnes 64) <<< 1
      rw [← BitVec.shiftLeft_and_distrib, BitVec.and_allOnes]
  · rw [BitVec.shiftLeft_and_distrib]
    calc
      _ = ((x >>> 1) &&& (x <<< 1)) &&&
        (0x5555555555555554#64 &&& (0x5555555555555555#64 <<< 1)) := by ac_rfl
      _ = 0 := by
        have h : 0x5555555555555554#64 &&& (0x5555555555555555#64 <<< (1 : Nat)) = 0 := by
          decide +kernel
        rw [h]
        simp only [BitVec.ofNat_eq_ofNat, BitVec.and_zero]

theorem reverseBits64_machine_clear (x : BitVec 64) :
    let a : BitVec 64 := bswapSpec x
    let b : BitVec 64 := ((a &&& 0x0f0f0f0f0f0f0f0f#64) <<< (4 : Nat)) |||
      ((a >>> (4 : Nat)) &&& 0x0f0f0f0f0f0f0f0f#64)
    let c : BitVec 64 := ((b >>> (2 : Nat)) &&& 0x3333333333333333#64) +
      ((b &&& 0x3333333333333333#64) <<< (2 : Nat))
    ((c >>> (1 : Nat)) &&& 0x5555555555555554#64) +
      ((c &&& 0x5555555555555555#64) <<< (1 : Nat)) =
      (x.reverse >>> (1 : Nat)) <<< (1 : Nat) := by
  dsimp only
  rw [reverseLast_clear, reverseBits64_machine]

theorem reverse_xor {w : Nat} (x y : BitVec w) :
    (x ^^^ y).reverse = x.reverse ^^^ y.reverse := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]

theorem reverse_xor_shift (x y : BitVec 64) :
    (x ^^^ y).reverse >>> (1 : Nat) =
      (x.reverse >>> (1 : Nat)) ^^^ (y.reverse >>> (1 : Nat)) :=
by
  rw [reverse_xor, BitVec.ushiftRight_xor_distrib]

theorem mask5555_comm (x : BitVec 64) :
    0x5555555555555555#64 &&& x = x &&& 0x5555555555555555#64 := BitVec.and_comm _ _


end AesGcm.Proofs.Machine.GHASHExecution
