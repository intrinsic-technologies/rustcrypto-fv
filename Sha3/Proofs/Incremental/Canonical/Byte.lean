import Sha3.Proofs.Incremental.State

namespace Sha3.Proofs.Incremental

open Keccak Absorption

theorem blockLanes_eq_zero_of_size_le (bytes : ByteArray) (offset rate : Nat)
    (h : bytes.size ≤ offset) : blockLanes bytes offset rate = fun _ ↦ 0#64 := by
  funext lane
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  have hread : ¬offset + (8 * lane.val + z / 8) < bytes.size := by omega
  simp [blockLanes, getLsbD_packLane _ ⟨z, hz⟩, hread]

theorem blockLanes_push_remainder (bytes : ByteArray) (byte : UInt8) (rate : Nat)
    (hr : 0 < rate) :
    blockLanes (bytes.push byte) (bytes.size / rate * rate) rate =
      fun lane ↦ blockLanes bytes (bytes.size / rate * rate) rate lane ^^^
        byteLanes (bytes.size % rate) byte lane := by
  have hmod := Nat.mod_lt bytes.size hr
  have hdiv := Nat.div_add_mod bytes.size rate
  rw [Nat.mul_comm rate] at hdiv
  funext lane
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [blockLanes, byteLanes, BitVec.getLsbD_xor,
    getLsbD_packLane _ ⟨z, hz⟩, ByteArray.size_push]
  by_cases hlt : 8 * lane.val + z / 8 < bytes.size % rate
  · have hj : 8 * lane.val + z / 8 < rate := by omega
    have hread : bytes.size / rate * rate + (8 * lane.val + z / 8) < bytes.size := by
      omega
    have hread' : bytes.size / rate * rate + (8 * lane.val + z / 8) <
        bytes.size + 1 := by omega
    have hne : ¬8 * lane.val + z / 8 = bytes.size % rate := by omega
    simp only [hj, hread, hread', and_self, ↓reduceDIte, hne, ↓reduceIte,
      ByteArray.data_push, Array.getElem_push_lt hread, Bool.xor_false]
  · by_cases heq : 8 * lane.val + z / 8 = bytes.size % rate
    · have hj : 8 * lane.val + z / 8 < rate := by omega
      have hread : ¬bytes.size / rate * rate + (8 * lane.val + z / 8) <
          bytes.size := by omega
      have hpos : bytes.size / rate * rate + (8 * lane.val + z / 8) =
          bytes.size := by omega
      have hread' : bytes.size / rate * rate + (8 * lane.val + z / 8) <
          bytes.size + 1 := by omega
      have hnot : ¬(8 * lane.val + z / 8 < rate ∧
          bytes.size / rate * rate + (8 * lane.val + z / 8) < bytes.size) := by omega
      have hyes : 8 * lane.val + z / 8 < rate ∧
          bytes.size / rate * rate + (8 * lane.val + z / 8) < bytes.size + 1 :=
        ⟨hj, hread'⟩
      simp only [dite_eq_left hyes, dite_eq_right hnot, ite_eq_left heq, Bool.false_xor,
        ByteArray.data_push]
      simpa only [hpos, ByteArray.size_data] using congrArg (fun b : UInt8 ↦ b.toBitVec.getLsbD (z % 8))
        (Array.getElem_push_eq (xs := bytes.data) (x := byte))
    · have hread : ¬bytes.size / rate * rate + (8 * lane.val + z / 8) <
          bytes.size := by omega
      have hread' : ¬bytes.size / rate * rate + (8 * lane.val + z / 8) <
          bytes.size + 1 := by omega
      simp [hread, hread', heq]

theorem canonicalState_empty (permute : Lanes → Lanes) (rate : Nat) :
    canonicalState permute rate ByteArray.empty = initial := by
  have hzero := blockLanes_eq_zero_of_size_le ByteArray.empty 0 rate (by decide)
  have hab : absorbBlocks permute rate ByteArray.empty = (fun _ ↦ 0#64) := by
    have hempty : (Array.ofFn fun i : Fin (ByteArray.empty.size / rate) ↦
        blockLanes ByteArray.empty (i.val * rate) rate) = #[] := by
      apply Array.eq_empty_of_size_eq_zero
      simp
    simp only [absorbBlocks, hempty, Array.foldl_empty]
  simp only [canonicalState, hab, ByteArray.size_empty, Nat.zero_div, Nat.zero_mul,
    Nat.zero_mod, hzero, BitVec.xor_zero, initial]

end Sha3.Proofs.Incremental
