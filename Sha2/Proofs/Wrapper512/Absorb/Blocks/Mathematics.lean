import Sha2.Proofs.Wrapper512.Absorb.Mathematics

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Blocks

open Sha2.Proofs.Common.SHA512

theorem split_message (prior bytes : ByteArray) (consumed : Nat) :
    (prior ++ bytes.extract 0 consumed) ++ bytes.extract consumed bytes.size = prior ++ bytes := by
  rw [ByteArray.append_assoc,ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _)]
  rw [ByteArray.extract_zero_max_size]

theorem finish_hash (hash : Array UInt64) (prior bytes : ByteArray) {consumed : Nat}
    (bound : consumed ≤ bytes.size)
    (aligned : (prior ++ bytes.extract 0 consumed).size % 128 = 0) :
    compressBlocks (compressBlocks hash (prior ++ bytes.extract 0 consumed))
      (bytes.extract consumed (consumed + 128 * ((bytes.size-consumed)/128))) =
      compressBlocks hash (prior ++ bytes) := by
  have suffixSize : (bytes.extract consumed bytes.size).size = bytes.size-consumed := by simp
  have blocks : fullBlocks (bytes.extract consumed bytes.size) =
      bytes.extract consumed (consumed + 128*((bytes.size-consumed)/128)) := by
    rw [fullBlocks,suffixSize,ByteArray.extract_extract]
    simp only [Nat.add_zero]
    rw [Nat.min_eq_left (by omega)]
  rw [← blocks, compressBlocks_fullBlocks, ← compressBlocks_append _ _ _ aligned,
    split_message]

theorem finish_counts (prior bytes : ByteArray) {consumed : Nat}
    (bound : consumed ≤ bytes.size)
    (aligned : (prior ++ bytes.extract 0 consumed).size % 128 = 0) :
    (prior ++ bytes).size/128 = (prior ++ bytes.extract 0 consumed).size/128 +
      (bytes.size-consumed)/128 ∧
    (prior ++ bytes).size%128 = (bytes.size-consumed)%128 := by
  have size : (prior ++ bytes.extract 0 consumed).size = prior.size+consumed := by
    rw [ByteArray.size_append,ByteArray.size_extract,Nat.min_eq_left bound,Nat.sub_zero]
  rw [size] at aligned ⊢
  rw [ByteArray.size_append]
  omega

theorem finish_tail (prior bytes : ByteArray) {consumed : Nat}
    (bound : consumed ≤ bytes.size)
    (aligned : (prior ++ bytes.extract 0 consumed).size % 128 = 0) :
    remainderBytes (prior ++ bytes) =
      bytes.extract (consumed + 128*((bytes.size-consumed)/128)) bytes.size := by
  rw [← split_message prior bytes consumed, remainderBytes_append_aligned _ _ aligned,
    remainderBytes,ByteArray.size_extract,Nat.min_self,ByteArray.extract_extract]
  rw [Nat.min_eq_right (by omega)]

end Sha2.Proofs.Wrapper512.Absorb.Blocks
