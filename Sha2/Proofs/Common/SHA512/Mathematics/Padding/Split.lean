import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Compression

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512
open Sha2.Proofs.NIST

theorem compressBlocksFrom_add (hash : Array UInt64) (input : ByteArray)
    (start first second : Nat) :
    compressBlocksFrom hash input start (first + second) =
      compressBlocksFrom (compressBlocksFrom hash input start first) input (start + first) second := by
  induction first generalizing hash start with
  | zero => simp only [Nat.zero_add, Nat.add_zero, compressBlocksFrom]
  | succ first ih =>
      rw [Nat.succ_add, compressBlocksFrom, compressBlocksFrom, ih]
      congr 1 <;> omega

theorem blockBits_append_left (a b : ByteArray) (i : Nat) (hi : i < a.size / 128) :
    blockBits (a ++ b) i = blockBits a i := by
  have hstart : 128 * i ≤ a.size := by omega
  have hstop : 128 * (i + 1) ≤ a.size := by omega
  simp only [blockBits, ByteArray.extract_append, Nat.sub_eq_zero_of_le hstart,
    Nat.sub_eq_zero_of_le hstop, ByteArray.extract_same, ByteArray.append_empty]

theorem blockBits_append_right (a b : ByteArray) (i : Nat) (ha : a.size % 128 = 0) :
    blockBits (a ++ b) (a.size / 128 + i) = blockBits b i := by
  have hs : 128 * (a.size / 128 + i) = a.size + 128 * i := by omega
  have he : 128 * (a.size / 128 + i + 1) = a.size + 128 * (i + 1) := by omega
  simp only [blockBits, hs, he, ByteArray.extract_append_size_add]

theorem compressBlocksFrom_append_left (hash : Array UInt64) (a b : ByteArray)
    (start count : Nat) (hcount : start + count ≤ a.size / 128) :
    compressBlocksFrom hash (a ++ b) start count = compressBlocksFrom hash a start count := by
  induction count generalizing hash start with
  | zero => rfl
  | succ count ih =>
      rw [compressBlocksFrom, compressBlocksFrom,
        blockBits_append_left a b start (by omega)]
      exact ih _ _ (by omega)

theorem compressBlocksFrom_append_right (hash : Array UInt64) (a b : ByteArray)
    (start count : Nat) (ha : a.size % 128 = 0) :
    compressBlocksFrom hash (a ++ b) (a.size / 128 + start) count =
      compressBlocksFrom hash b start count := by
  induction count generalizing hash start with
  | zero => rfl
  | succ count ih =>
      rw [compressBlocksFrom, compressBlocksFrom, blockBits_append_right a b start ha]
      rw [Nat.add_assoc]
      exact ih _ _

theorem compressBlocks_append (hash : Array UInt64) (a b : ByteArray) (ha : a.size % 128 = 0) :
    compressBlocks hash (a ++ b) = compressBlocks (compressBlocks hash a) b := by
  have hsize : (a ++ b).size / 128 = a.size / 128 + b.size / 128 := by
    rw [ByteArray.size_append]
    omega
  unfold compressBlocks
  rw [hsize, compressBlocksFrom_add, Nat.zero_add,
    compressBlocksFrom_append_left hash a b 0 (a.size / 128) (by omega)]
  simpa only [Nat.add_zero] using
    compressBlocksFrom_append_right (compressBlocksFrom hash a 0 (a.size / 128)) a b 0 (b.size / 128) ha

end Sha2.Proofs.Common.SHA512
