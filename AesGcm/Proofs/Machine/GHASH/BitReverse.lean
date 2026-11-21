import Std

namespace AesGcm.Proofs.Machine.GHASH

def swapBytes64 (x : BitVec 64) : BitVec 64 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8 ++
    x.extractLsb' 32 8 ++ x.extractLsb' 40 8 ++ x.extractLsb' 48 8 ++ x.extractLsb' 56 8

def reverseBits64 (x : BitVec 64) : BitVec 64 :=
  let a : BitVec 64 := swapBytes64 x
  let b : BitVec 64 := ((a >>> (4 : Nat)) &&& 0x0f0f0f0f0f0f0f0f#64) ||| ((a &&& 0x0f0f0f0f0f0f0f0f#64) <<< (4 : Nat))
  let c : BitVec 64 := ((b >>> (2 : Nat)) &&& 0x3333333333333333#64) + ((b &&& 0x3333333333333333#64) <<< (2 : Nat))
  ((c >>> (1 : Nat)) &&& 0x5555555555555555#64) + ((c &&& 0x5555555555555555#64) <<< (1 : Nat))

theorem maskedSwap_add_eq_or (x m : BitVec 64) (n : Nat) (h : m &&& (m <<< n) = 0) :
    ((x >>> n) &&& m) + ((x &&& m) <<< n) =
      ((x >>> n) &&& m) ||| ((x &&& m) <<< n) := by
  apply BitVec.add_eq_or_of_and_eq_zero
  rw [BitVec.shiftLeft_and_distrib]
  calc
    _ = ((x >>> n) &&& (x <<< n)) &&& (m &&& (m <<< n)) := by ac_rfl
    _ = 0 := by rw [h]; simp

theorem reverseBits64_eq_reverse (x : BitVec 64) : reverseBits64 x = x.reverse := by
  simp only [reverseBits64]
  rw [maskedSwap_add_eq_or _ 0x5555555555555555#64 1 (by decide +kernel),
    maskedSwap_add_eq_or _ 0x3333333333333333#64 2 (by decide +kernel)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
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
    simp only [swapBytes64, BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD,
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_ofNat] <;> simp [Nat.testBit_eq_decide_div_mod_eq]


end AesGcm.Proofs.Machine.GHASH
