import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Tail

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb

open Sha2.Proofs.Common.SHA512

theorem compressBlocks_append_buffered (hash : Array UInt64) (a b : ByteArray) :
    compressBlocks hash (a ++ b) =
      compressBlocks (compressBlocks hash a) (remainderBytes a ++ b) := by
  conv => lhs; rw [← fullBlocks_append_remainderBytes a, ByteArray.append_assoc]
  rw [compressBlocks_append _ _ _ (by rw [fullBlocks_size]; omega), compressBlocks_fullBlocks]

theorem remainderBytes_append_aligned (a b : ByteArray) (ha : a.size % 128 = 0) :
    remainderBytes (a ++ b) = remainderBytes b := by
  have hs : 128*((a.size+b.size)/128) = a.size+128*(b.size/128) := by omega
  simp only [remainderBytes, ByteArray.size_append, hs, ByteArray.extract_append_size_add]

theorem remainderBytes_append_buffered (a b : ByteArray) :
    remainderBytes (a ++ b) = remainderBytes (remainderBytes a ++ b) := by
  conv => lhs; rw [← fullBlocks_append_remainderBytes a, ByteArray.append_assoc]
  exact remainderBytes_append_aligned _ _ (by rw [fullBlocks_size]; omega)

theorem compressBlocks_short (hash : Array UInt64) (input : ByteArray) (h : input.size < 128) :
    compressBlocks hash input = hash := by
  simp only [compressBlocks, Nat.div_eq_of_lt h, compressBlocksFrom]

theorem remainderBytes_short (input : ByteArray) (h : input.size < 128) :
    remainderBytes input = input := by
  simp only [remainderBytes, Nat.div_eq_of_lt h, Nat.mul_zero, ByteArray.extract_zero_size]

theorem compressBlocks_append_short (hash : Array UInt64) (a b : ByteArray)
    (h : b.size < 128 - a.size % 128) :
    compressBlocks hash (a ++ b) = compressBlocks hash a := by
  rw [compressBlocks_append_buffered, compressBlocks_short]
  rw [ByteArray.size_append, remainderBytes_size]
  omega

theorem remainderBytes_append_short (a b : ByteArray) (h : b.size < 128 - a.size % 128) :
    remainderBytes (a ++ b) = remainderBytes a ++ b := by
  rw [remainderBytes_append_buffered, remainderBytes_short]
  rw [ByteArray.size_append, remainderBytes_size]
  omega

def filledBlock (a b : ByteArray) : ByteArray :=
  remainderBytes a ++ b.extract 0 (128 - a.size % 128)

def afterFilledBlock (a b : ByteArray) : ByteArray :=
  b.extract (128 - a.size % 128) b.size

theorem filledBlock_size (a b : ByteArray) (h : 128 - a.size % 128 ≤ b.size) :
    (filledBlock a b).size = 128 := by
  simp only [filledBlock, ByteArray.size_append, remainderBytes_size, ByteArray.size_extract,
    Nat.min_eq_left h, Nat.sub_zero]
  omega

theorem filledBlock_append_after (a b : ByteArray) :
    filledBlock a b ++ afterFilledBlock a b = remainderBytes a ++ b := by
  simp only [filledBlock, afterFilledBlock, ByteArray.append_assoc]
  congr 1
  rw [ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
    ByteArray.extract_zero_max_size]

theorem compressBlocks_append_filled (hash : Array UInt64) (a b : ByteArray)
    (h : 128 - a.size % 128 ≤ b.size) :
    compressBlocks hash (a ++ b) =
      compressBlocks (NIST.SHA512.compress (compressBlocks hash a)
        (NIST.Encoding.octetsToBits (filledBlock a b))) (afterFilledBlock a b) := by
  rw [compressBlocks_append_buffered, ← filledBlock_append_after,
    compressBlocks_append _ _ _ (by rw [filledBlock_size a b h]),
    compressBlocks_single _ _ (filledBlock_size a b h)]

theorem remainderBytes_append_filled (a b : ByteArray) (h : 128 - a.size % 128 ≤ b.size) :
    remainderBytes (a ++ b) = remainderBytes (afterFilledBlock a b) := by
  rw [remainderBytes_append_buffered, ← filledBlock_append_after]
  exact remainderBytes_append_aligned _ _ (by rw [filledBlock_size a b h])

theorem afterFilledBlock_size (a b : ByteArray) :
    (afterFilledBlock a b).size = b.size - (128 - a.size % 128) := by
  simp only [afterFilledBlock, ByteArray.size_extract, Nat.min_self]

theorem append_short_counts (a b : ByteArray) (h : b.size < 128 - a.size % 128) :
    (a ++ b).size / 128 = a.size / 128 ∧
      (a ++ b).size % 128 = a.size % 128 + b.size := by
  rw [ByteArray.size_append]
  omega

theorem append_filled_counts (a b : ByteArray) (h : 128 - a.size % 128 ≤ b.size) :
    (a ++ b).size / 128 = a.size / 128 + 1 + (afterFilledBlock a b).size / 128 ∧
      (a ++ b).size % 128 = (afterFilledBlock a b).size % 128 := by
  rw [ByteArray.size_append, afterFilledBlock_size]
  omega

theorem compressBlocks_filled_prefix (hash : Array UInt64) (a b : ByteArray)
    (h : 128-a.size%128 ≤ b.size) :
    compressBlocks hash (a ++ b.extract 0 (128-a.size%128)) =
      NIST.SHA512.compress (compressBlocks hash a) (NIST.Encoding.octetsToBits (filledBlock a b)) := by
  rw [compressBlocks_append_buffered]
  exact compressBlocks_single _ _ (filledBlock_size a b h)

theorem filled_prefix_counts (a b : ByteArray) (h : 128-a.size%128 ≤ b.size) :
    (a ++ b.extract 0 (128-a.size%128)).size%128 = 0 ∧
    (a ++ b.extract 0 (128-a.size%128)).size/128 = a.size/128+1 := by
  rw [ByteArray.size_append,ByteArray.size_extract,Nat.min_eq_left h,Nat.sub_zero]
  omega

end Sha2.Proofs.Wrapper512.Absorb
