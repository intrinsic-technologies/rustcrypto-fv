import AesGcm.Proofs.Machine.AESCore.Rows
import AesGcm.Proofs.Machine.KeySchedule.Layout
import AesGcm.Proofs.Machine.Fixslice.Linear
import AesGcm.Proofs.Machine.Fixslice.MixColumns
import AesGcm.Proofs.Machine.Common.MixColumns

namespace AesGcm.Proofs.Machine.AESCore

open Standards.NIST.AES AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.KeySchedule

theorem invRowsPow_eq_shiftRowsBy (n : Nat) (block : Block) :
    invRowsPow n block = shiftRowsBy (3 * n) block := by
  induction n with
  | zero => exact (shiftRowsBy_zero block).symm
  | succ n ih =>
    rw [invRowsPow, ih, ← shiftRowsBy_three, shiftRowsBy_add]
    congr 1
    omega

theorem fromStandard_shiftRowsBy (n : Nat) (x : StandardBlocks) :
    shiftRowsBlocks n (fromStandard x) = fromStandard (fun b ↦ shiftRowsBy n (x b)) := by
  funext b j
  simp only [shiftRowsBlocks, fromStandard, shiftRowsBy, Vector.getElem_ofFn,
    Fin.getElem_fin, rowIndex]
  congr 2
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  omega

theorem shiftRows1_encodeStandard (x : StandardBlocks) :
    shiftRows1 (encodeStandard x) = encodeStandard (fun b ↦ shiftRowsBy 1 (x b)) := by
  simp only [encodeStandard, shiftRows1_encode, fromStandard_shiftRowsBy]

theorem shiftRows2_encodeStandard (x : StandardBlocks) :
    shiftRows2 (encodeStandard x) = encodeStandard (fun b ↦ shiftRowsBy 2 (x b)) := by
  simp only [encodeStandard, shiftRows2_encode, fromStandard_shiftRowsBy]

theorem shiftRows3_encodeStandard (x : StandardBlocks) :
    shiftRows3 (encodeStandard x) = encodeStandard (fun b ↦ shiftRowsBy 3 (x b)) := by
  simp only [encodeStandard, shiftRows3_encode, fromStandard_shiftRowsBy]

def phase (round : Nat) (x : StandardBlocks) : StandardBlocks :=
  fun b ↦ invRowsPow (round % 4) (x b)

def phaseEncode (round : Nat) (x : StandardBlocks) : Planes := encodeStandard (phase round x)

theorem phase_zero (x : StandardBlocks) : phase 0 x = x := rfl

theorem phase_mod (round : Nat) (x : StandardBlocks) :
    phase (round % 4) x = phase round x := by
  funext b
  change invRowsPow ((round % 4) % 4) (x b) = invRowsPow (round % 4) (x b)
  rw [Nat.mod_mod]

theorem phase_subBytes (round : Nat) (x : StandardBlocks) :
    phase round (fun b ↦ Standards.NIST.AES.subBytes (x b)) =
      fun b ↦ Standards.NIST.AES.subBytes (phase round x b) := by
  funext b
  simp only [phase, invRowsPow_eq_shiftRowsBy, shiftRowsBy_subBytes]

theorem phase_succ_shiftRows (round : Nat) (x : StandardBlocks) :
    phase (round + 1) (fun b ↦ shiftRows (x b)) = phase round x := by
  funext b
  simp only [phase, invRowsPow_eq_shiftRowsBy, ← shiftRowsBy_one, shiftRowsBy_add]
  rw [← shiftRowsBy_mod (3 * ((round + 1) % 4) + 1),
    ← shiftRowsBy_mod (3 * (round % 4))]
  congr 1
  omega

theorem phaseEncode_zero (x : StandardBlocks) : phaseEncode 0 x = encodeStandard x := rfl

theorem phaseEncode_mod (round : Nat) (x : StandardBlocks) :
    phaseEncode (round % 4) x = phaseEncode round x := by
  simp only [phaseEncode, phase_mod]

theorem rowIndex_rotateByteIndex (i n : Fin 4) (j : Fin 16) :
    rowIndex (3 * i.val) (rotateByteIndex n.val (n.val * i.val) j) =
      rotateByteIndex n.val 0 (rowIndex (3 * i.val) j) := by
  decide +kernel +revert

theorem mixColumnsBlocks_phase (i : Fin 4) (x : StandardBlocks) :
    mixColumnsBlocks (rotateBlocks 1 i.val) (rotateBlocks 2 (2 * i.val))
      (fromStandard (phase i.val x)) =
        fromStandard (phase i.val (fun b ↦ Standards.NIST.AES.mixColumns (x b))) := by
  funext b j
  change (UInt8.ofBitVec
    (mixColumnsBlocks (rotateBlocks 1 i.val) (rotateBlocks 2 (2 * i.val))
      (fromStandard (phase i.val x)) b j)).toBitVec = _
  rw [mixColumnsBlocks_rotate_get]
  simp only [fromStandard, phase, Nat.mod_eq_of_lt i.isLt, invRowsPow_eq_shiftRowsBy,
    shiftRowsBy, Vector.getElem_ofFn, UInt8.ofBitVec_toBitVec]
  change (mul 2 (x b)[rowIndex (3 * i.val) j] ^^^
    mul 3 (x b)[rowIndex (3 * i.val) (rotateByteIndex 1 i.val j)] ^^^
    mul 1 (x b)[rowIndex (3 * i.val) (rotateByteIndex 2 (2 * i.val) j)] ^^^
    mul 1 (x b)[rowIndex (3 * i.val) (rotateByteIndex 3 (3 * i.val) j)]).toBitVec =
      (Standards.NIST.AES.mixColumns (x b))[rowIndex (3 * i.val) j].toBitVec
  have h1 := rowIndex_rotateByteIndex i 1 j
  simp only [Fin.val_one, Nat.one_mul] at h1
  have h2 := rowIndex_rotateByteIndex i 2 j
  change rowIndex (3 * i.val) (rotateByteIndex 2 (2 * i.val) j) =
    rotateByteIndex 2 0 (rowIndex (3 * i.val) j) at h2
  have h3 := rowIndex_rotateByteIndex i 3 j
  change rowIndex (3 * i.val) (rotateByteIndex 3 (3 * i.val) j) =
    rotateByteIndex 3 0 (rowIndex (3 * i.val) j) at h3
  simp only [h1, h2, h3]
  simp only [Standards.NIST.AES.mixColumns, mixColumnsWith, Vector.getElem_ofFn,
    Fin.getElem_fin, rotateByteIndex]
  congr 5
  all_goals first | omega | (congr 1 <;> omega)

theorem mixColumnsBlocks_xor63 (k : Nat) (x : Blocks) :
    mixColumnsBlocks (rotateBlocks 1 k) (rotateBlocks 2 (2 * k))
      (xorBlocks x (fun _ _ ↦ 0x63)) =
        xorBlocks (mixColumnsBlocks (rotateBlocks 1 k) (rotateBlocks 2 (2 * k)) x)
          (fun _ _ ↦ 0x63) := by
  funext b j
  change (UInt8.ofBitVec
    (mixColumnsBlocks (rotateBlocks 1 k) (rotateBlocks 2 (2 * k))
      (xorBlocks x (fun _ _ ↦ 0x63)) b j)).toBitVec =
        (UInt8.ofBitVec
          (xorBlocks (mixColumnsBlocks (rotateBlocks 1 k) (rotateBlocks 2 (2 * k)) x)
            (fun _ _ ↦ 0x63) b j)).toBitVec
  apply congrArg UInt8.toBitVec
  simp only [mixColumnsBlocks_rotate_get, xorBlocks, UInt8.ofBitVec_xor,
    AesGcm.Proofs.Machine.mul_xor_right]
  have h : mul 2 0x63 ^^^ mul 3 0x63 ^^^ mul 1 0x63 ^^^ mul 1 0x63 = (0x63 : UInt8) :=
    by decide +kernel
  change _ = _ ^^^ (0x63 : UInt8)
  conv => rhs; rw [← h]
  ac_rfl

theorem rotateBlocks_mod (r c : Nat) :
    rotateBlocks r c = rotateBlocks (r % 4) (c % 4) := by
  funext x b j
  apply congrArg (x b)
  apply Fin.ext
  simp only [rotateByteIndex, Fin.val_mk, Nat.add_mod, Nat.mod_mod]

end AesGcm.Proofs.Machine.AESCore
