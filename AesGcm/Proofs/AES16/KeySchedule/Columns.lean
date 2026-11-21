import AesGcm.Proofs.Machine.Fixslice.Linear

namespace AesGcm.Proofs.Machine.KeySchedule

open AesGcm.Proofs.Machine.Fixslice

def xorColumnsWord (previous substituted : BitVec 64) (rotation : Nat) : BitVec 64 :=
  let rk := previous ^^^ (uniformRow 0x03 &&& substituted.rotateRight rotation)
  rk ^^^ (uniformRow 0xfc &&& (rk <<< 4)) ^^^
    (uniformRow 0xf0 &&& (rk <<< 8)) ^^^ (uniformRow 0xc0 &&& (rk <<< 12))

def xorColumns (previous substituted : Planes) (rotation : Nat) : Planes :=
  fun p ↦ xorColumnsWord (previous p) (substituted p) rotation

def xorColumnsBlocks (previous substituted : Blocks) (rows : Nat) : Blocks := fun b j ↦
  let r := j.val % 4
  let c := j.val / 4
  let x0 := previous b ⟨r, by omega⟩ ^^^
    substituted b ⟨12 + (r + rows) % 4, by omega⟩
  let x1 := x0 ^^^ previous b ⟨4 + r, by omega⟩
  let x2 := x1 ^^^ previous b ⟨8 + r, by omega⟩
  if c = 0 then x0 else if c = 1 then x1 else if c = 2 then x2
  else x2 ^^^ previous b ⟨12 + r, by omega⟩

private theorem bne_left_comm (x y z : Bool) :
    (x != (y != z)) = (y != (x != z)) := by decide +kernel +revert

private theorem bne_comm (x y : Bool) : (x != y) = (y != x) := by
  decide +kernel +revert


theorem encode_bit (x : Blocks) (p : Fin 8) (i : Nat) :
    (encode x p).getLsbD i = if h : i < 64 then
      (x ⟨i % 4, by omega⟩ ⟨4 * (i / 4 % 4) + i / 16, by omega⟩).getLsbD p.val
      else false := by
  split
  · exact getLsbD_encode x p ⟨i, by assumption⟩
  · exact BitVec.getLsbD_of_ge _ _ (by omega)

set_option maxHeartbeats 2400000 in
theorem xorColumns_encode (previous substituted : Blocks) (rows : Fin 2) :
    xorColumns (encode previous) (encode substituted) (16 * rows.val + 12) =
      encode (xorColumnsBlocks previous substituted rows.val) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hr : rows.val = 0 ∨ rows.val = 1 := by omega
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hr with hr | hr
  all_goals rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  all_goals simp only [hc, hr, xorColumns, xorColumnsWord, uniformRow, doubleBits,
    BitVec.ofNat_eq_ofNat, BitVec.truncate_eq_setWidth, Nat.reduceLeDiff, Nat.reducePow,
    Nat.reduceLT, BitVec.setWidth_ofNat_of_le_of_lt, BitVec.reduceHShiftLeft, BitVec.reduceOr,
    BitVec.reduceAnd, BitVec.reduceMul, BitVec.getLsbD_xor, encode_bit, Nat.zero_lt_succ,
    Nat.lt_add_one, ↓reduceDIte, Nat.zero_mod, Fin.zero_eta, Fin.isValue, Nat.zero_div,
    Nat.mul_zero, Nat.add_zero, BitVec.getLsbD_and, BitVec.reduceGetLsb,
    BitVec.getLsbD_rotateRight, Nat.reduceMod, Nat.reduceSub, ↓reduceIte, Nat.reduceDiv,
    Nat.mod_succ, Nat.reduceMul, Fin.reduceFinMk, Bool.true_and, BitVec.getLsbD_shiftLeft,
    decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.and_false, Nat.zero_le,
    Nat.sub_eq_zero_of_le, Bool.false_and, Bool.and_self, bne_comm, Bool.false_bne,
    xorColumnsBlocks, Nat.reduceAdd, Nat.mul_one, Nat.mod_self, Nat.zero_add, Fin.mk_one,
    bne_left_comm, Bool.bne_assoc, reduceCtorEq, Nat.reduceEqDiff, Nat.succ_ne_self]


end AesGcm.Proofs.Machine.KeySchedule
