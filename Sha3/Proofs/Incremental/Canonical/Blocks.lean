import Sha3.Proofs.Incremental.State

namespace Sha3.Proofs.Incremental

open Keccak Absorption

theorem blockLanes_push_of_le (bytes : ByteArray) (byte : UInt8) (offset rate : Nat)
    (h : offset + rate ≤ bytes.size) :
    blockLanes (bytes.push byte) offset rate = blockLanes bytes offset rate := by
  rw [← ByteArray.append_toByteArray_singleton]
  exact blockLanes_append_of_le bytes [byte].toByteArray offset rate h

theorem absorbBlocks_push_of_mod_ne (permute : Lanes → Lanes) (rate : Nat)
    (hr : 0 < rate) (bytes : ByteArray) (byte : UInt8)
    (h : bytes.size % rate + 1 ≠ rate) :
    absorbBlocks permute rate (bytes.push byte) = absorbBlocks permute rate bytes := by
  have hsize : (bytes.push byte).size / rate = bytes.size / rate := by
    rw [ByteArray.size_push]
    apply Nat.div_eq_of_lt_le
    · have := Nat.div_mul_le_self bytes.size rate
      omega
    · have hmod := Nat.mod_lt bytes.size hr
      have hdiv := Nat.div_add_mod bytes.size rate
      rw [Nat.mul_comm rate] at hdiv
      simp only [Nat.add_mul, Nat.one_mul]
      omega
  have hblocks :
      (Array.ofFn fun i : Fin ((bytes.push byte).size / rate) ↦
        blockLanes (bytes.push byte) (i.val * rate) rate) =
      (Array.ofFn fun i : Fin (bytes.size / rate) ↦
        blockLanes bytes (i.val * rate) rate) := by
    apply Array.ext
    · simp only [Array.size_ofFn, hsize]
    · intro i hi hj
      simp only [Array.size_ofFn] at hj
      simp only [Array.getElem_ofFn]
      apply blockLanes_push_of_le
      have hblock : (i + 1) * rate ≤ bytes.size :=
        Nat.le_trans (Nat.mul_le_mul_right rate hj) (Nat.div_mul_le_self bytes.size rate)
      simpa only [Nat.add_mul, Nat.one_mul] using hblock
  simp only [absorbBlocks, hblocks]

theorem absorbBlocks_push_of_mod_eq (permute : Lanes → Lanes) (rate : Nat)
    (hr : 0 < rate) (bytes : ByteArray) (byte : UInt8)
    (h : bytes.size % rate + 1 = rate) :
    absorbBlocks permute rate (bytes.push byte) =
      permute (fun lane ↦ absorbBlocks permute rate bytes lane ^^^
        blockLanes (bytes.push byte) (bytes.size / rate * rate) rate lane) := by
  have hsize : (bytes.push byte).size / rate = bytes.size / rate + 1 := by
    rw [ByteArray.size_push]
    have hlen : bytes.size + 1 = (bytes.size / rate + 1) * rate := by
      have hdiv := Nat.div_add_mod bytes.size rate
      rw [Nat.mul_comm rate] at hdiv
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    rw [hlen, Nat.mul_div_cancel _ hr]
  have hblocks :
      (Array.ofFn fun i : Fin ((bytes.push byte).size / rate) ↦
        blockLanes (bytes.push byte) (i.val * rate) rate) =
      (Array.ofFn fun i : Fin (bytes.size / rate) ↦
        blockLanes bytes (i.val * rate) rate).push
          (blockLanes (bytes.push byte) (bytes.size / rate * rate) rate) := by
    apply Array.ext
    · simp only [Array.size_ofFn, Array.size_push, hsize]
    · intro i hi hj
      simp only [Array.size_ofFn, hsize] at hi
      simp only [Array.getElem_ofFn, Array.getElem_push, Array.size_ofFn]
      by_cases hilt : i < bytes.size / rate
      · simp only [hilt, ↓reduceDIte]
        apply blockLanes_push_of_le
        have hblock : (i + 1) * rate ≤ bytes.size :=
          Nat.le_trans (Nat.mul_le_mul_right rate hilt) (Nat.div_mul_le_self bytes.size rate)
        simpa only [Nat.add_mul, Nat.one_mul] using hblock
      · have hiq : i = bytes.size / rate := by omega
        simp [hiq]
  simp only [absorbBlocks]
  rw [hblocks, Array.foldl_push]

end Sha3.Proofs.Incremental
