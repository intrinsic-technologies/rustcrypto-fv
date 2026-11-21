import Sha2.Proofs.Wrapper.Absorb.Mathematics

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Blocks

open Sha2.Proofs.Common.SHA256

theorem split_message (prior bytes : ByteArray) (consumed : Nat) :
    (prior ++ bytes.extract 0 consumed) ++ bytes.extract consumed bytes.size = prior ++ bytes := by
  rw [ByteArray.append_assoc,ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _)]
  rw [ByteArray.extract_zero_max_size]

theorem finish_hash (hash : Array UInt32) (prior bytes : ByteArray) {consumed : Nat}
    (bound : consumed ≤ bytes.size)
    (aligned : (prior ++ bytes.extract 0 consumed).size % 64 = 0) :
    compressBlocks (compressBlocks hash (prior ++ bytes.extract 0 consumed))
      (bytes.extract consumed (consumed + 64 * ((bytes.size-consumed)/64))) =
      compressBlocks hash (prior ++ bytes) := by
  have suffixSize : (bytes.extract consumed bytes.size).size = bytes.size-consumed := by simp
  have blocks : fullBlocks (bytes.extract consumed bytes.size) =
      bytes.extract consumed (consumed + 64*((bytes.size-consumed)/64)) := by
    rw [fullBlocks,suffixSize,ByteArray.extract_extract]
    simp only [Nat.add_zero]
    rw [Nat.min_eq_left (by omega)]
  rw [← blocks, compressBlocks_fullBlocks, ← compressBlocks_append _ _ _ aligned,
    split_message]

theorem finish_counts (prior bytes : ByteArray) {consumed : Nat}
    (bound : consumed ≤ bytes.size)
    (aligned : (prior ++ bytes.extract 0 consumed).size % 64 = 0) :
    (prior ++ bytes).size/64 = (prior ++ bytes.extract 0 consumed).size/64 +
      (bytes.size-consumed)/64 ∧
    (prior ++ bytes).size%64 = (bytes.size-consumed)%64 := by
  have size : (prior ++ bytes.extract 0 consumed).size = prior.size+consumed := by
    rw [ByteArray.size_append,ByteArray.size_extract,Nat.min_eq_left bound,Nat.sub_zero]
  rw [size] at aligned ⊢
  rw [ByteArray.size_append]
  omega

theorem finish_tail (prior bytes : ByteArray) {consumed : Nat}
    (bound : consumed ≤ bytes.size)
    (aligned : (prior ++ bytes.extract 0 consumed).size % 64 = 0) :
    remainderBytes (prior ++ bytes) =
      bytes.extract (consumed + 64*((bytes.size-consumed)/64)) bytes.size := by
  rw [← split_message prior bytes consumed, remainderBytes_append_aligned _ _ aligned,
    remainderBytes,ByteArray.size_extract,Nat.min_self,ByteArray.extract_extract]
  rw [Nat.min_eq_right (by omega)]

end Sha2.Proofs.Wrapper.Absorb.Blocks
