import Sha3.Proofs.Update.FullBlocks.Loop
import Sha3.Proofs.Incremental.Chunks

namespace Sha3.Proofs.Update

open Keccak Absorption

theorem blockLanes_extract (bytes : ByteArray) (offset rate : Nat)
    (h : offset + rate ≤ bytes.size) :
    blockLanes (bytes.extract offset (offset + rate)) 0 rate = blockLanes bytes offset rate := by
  have hsize : (bytes.extract offset (offset + rate)).size = rate := by
    rw [ByteArray.size_extract, Nat.min_eq_left h]
    omega
  funext lane
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [blockLanes, getLsbD_packLane _ ⟨z, hz⟩, Nat.zero_add]
  by_cases hj : 8 * lane.val + z / 8 < rate
  · have hi : offset + (8 * lane.val + z / 8) < bytes.size := by omega
    have hj' : 8 * lane.val + z / 8 < (bytes.extract offset (offset + rate)).size := by
      rw [hsize]
      exact hj
    simp only [hj, hj', hi, and_self, ↓reduceDIte]
    congr 2
    exact ByteArray.getElem_extract _
  · simp only [hj, false_and, ↓reduceDIte]

theorem update_full_blocks (bytes : ByteArray) (a : Lanes) (rate offset count : Nat)
    (hr : 0 < rate) (hsize : offset + count * rate ≤ bytes.size) :
    Incremental.update keccakLanes rate ⟨a, 0⟩
        (bytes.extract offset (offset + count * rate)) =
      ⟨FullBlocks.absorbedPrefix a rate bytes offset count, 0⟩ := by
  induction count with
  | zero =>
    rw [Nat.zero_mul, Nat.add_zero,
      ByteArray.extract_eq_empty_iff.mpr (Nat.min_le_left _ _),
      Incremental.update_empty, FullBlocks.absorbedPrefix_zero]
  | succ count ih =>
    have hp : offset + count * rate ≤ bytes.size := by
      rw [Nat.succ_mul] at hsize
      omega
    have hb : offset + count * rate + rate ≤ bytes.size := by
      simpa only [Nat.succ_mul, Nat.add_assoc] using hsize
    rw [ByteArray.extract_eq_extract_append_extract (offset + count * rate)
      (by omega) (by rw [Nat.succ_mul]; omega), Incremental.update_append, ih hp]
    have he : offset + (count + 1) * rate = offset + count * rate + rate := by
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [he]
    rw [Incremental.update_block _ _ _ _ hr (by
      rw [ByteArray.size_extract, Nat.min_eq_left hb]
      omega), blockLanes_extract bytes (offset + count * rate) rate hb,
      FullBlocks.absorbedPrefix_succ]

end Sha3.Proofs.Update
