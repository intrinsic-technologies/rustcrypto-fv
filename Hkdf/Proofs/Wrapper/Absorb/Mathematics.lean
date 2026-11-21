import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Tail

set_option autoImplicit false

namespace Hkdf.Proofs.Wrapper.Absorb

open Hkdf.Proofs.Common.SHA256

theorem compressBlocks_append_buffered (hash : Array UInt32) (a b : ByteArray) :
    compressBlocks hash (a ++ b) =
      compressBlocks (compressBlocks hash a) (remainderBytes a ++ b) := by
  conv => lhs; rw [← fullBlocks_append_remainderBytes a, ByteArray.append_assoc]
  rw [compressBlocks_append _ _ _ (by rw [fullBlocks_size]; omega), compressBlocks_fullBlocks]

theorem remainderBytes_append_aligned (a b : ByteArray) (ha : a.size % 64 = 0) :
    remainderBytes (a ++ b) = remainderBytes b := by
  have hs : 64*((a.size+b.size)/64) = a.size+64*(b.size/64) := by omega
  simp only [remainderBytes, ByteArray.size_append, hs, ByteArray.extract_append_size_add]

theorem remainderBytes_append_buffered (a b : ByteArray) :
    remainderBytes (a ++ b) = remainderBytes (remainderBytes a ++ b) := by
  conv => lhs; rw [← fullBlocks_append_remainderBytes a, ByteArray.append_assoc]
  exact remainderBytes_append_aligned _ _ (by rw [fullBlocks_size]; omega)

theorem compressBlocks_short (hash : Array UInt32) (input : ByteArray) (h : input.size < 64) :
    compressBlocks hash input = hash := by
  simp only [compressBlocks, Nat.div_eq_of_lt h, compressBlocksFrom]

theorem remainderBytes_short (input : ByteArray) (h : input.size < 64) :
    remainderBytes input = input := by
  simp only [remainderBytes, Nat.div_eq_of_lt h, Nat.mul_zero, ByteArray.extract_zero_size]

theorem compressBlocks_append_short (hash : Array UInt32) (a b : ByteArray)
    (h : b.size < 64 - a.size % 64) :
    compressBlocks hash (a ++ b) = compressBlocks hash a := by
  rw [compressBlocks_append_buffered, compressBlocks_short]
  rw [ByteArray.size_append, remainderBytes_size]
  omega

theorem remainderBytes_append_short (a b : ByteArray) (h : b.size < 64 - a.size % 64) :
    remainderBytes (a ++ b) = remainderBytes a ++ b := by
  rw [remainderBytes_append_buffered, remainderBytes_short]
  rw [ByteArray.size_append, remainderBytes_size]
  omega

def filledBlock (a b : ByteArray) : ByteArray :=
  remainderBytes a ++ b.extract 0 (64 - a.size % 64)

def afterFilledBlock (a b : ByteArray) : ByteArray :=
  b.extract (64 - a.size % 64) b.size

theorem filledBlock_size (a b : ByteArray) (h : 64 - a.size % 64 ≤ b.size) :
    (filledBlock a b).size = 64 := by
  simp only [filledBlock, ByteArray.size_append, remainderBytes_size, ByteArray.size_extract,
    Nat.min_eq_left h, Nat.sub_zero]
  omega

theorem filledBlock_append_after (a b : ByteArray) :
    filledBlock a b ++ afterFilledBlock a b = remainderBytes a ++ b := by
  simp only [filledBlock, afterFilledBlock, ByteArray.append_assoc]
  congr 1
  rw [ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
    ByteArray.extract_zero_max_size]

theorem compressBlocks_append_filled (hash : Array UInt32) (a b : ByteArray)
    (h : 64 - a.size % 64 ≤ b.size) :
    compressBlocks hash (a ++ b) =
      compressBlocks (NIST.SHA256.compress (compressBlocks hash a)
        (NIST.Encoding.octetsToBits (filledBlock a b))) (afterFilledBlock a b) := by
  rw [compressBlocks_append_buffered, ← filledBlock_append_after,
    compressBlocks_append _ _ _ (by rw [filledBlock_size a b h]),
    compressBlocks_single _ _ (filledBlock_size a b h)]

theorem remainderBytes_append_filled (a b : ByteArray) (h : 64 - a.size % 64 ≤ b.size) :
    remainderBytes (a ++ b) = remainderBytes (afterFilledBlock a b) := by
  rw [remainderBytes_append_buffered, ← filledBlock_append_after]
  exact remainderBytes_append_aligned _ _ (by rw [filledBlock_size a b h])

theorem afterFilledBlock_size (a b : ByteArray) :
    (afterFilledBlock a b).size = b.size - (64 - a.size % 64) := by
  simp only [afterFilledBlock, ByteArray.size_extract, Nat.min_self]

theorem append_short_counts (a b : ByteArray) (h : b.size < 64 - a.size % 64) :
    (a ++ b).size / 64 = a.size / 64 ∧
      (a ++ b).size % 64 = a.size % 64 + b.size := by
  rw [ByteArray.size_append]
  omega

theorem append_filled_counts (a b : ByteArray) (h : 64 - a.size % 64 ≤ b.size) :
    (a ++ b).size / 64 = a.size / 64 + 1 + (afterFilledBlock a b).size / 64 ∧
      (a ++ b).size % 64 = (afterFilledBlock a b).size % 64 := by
  rw [ByteArray.size_append, afterFilledBlock_size]
  omega

theorem compressBlocks_filled_prefix (hash : Array UInt32) (a b : ByteArray)
    (h : 64-a.size%64 ≤ b.size) :
    compressBlocks hash (a ++ b.extract 0 (64-a.size%64)) =
      NIST.SHA256.compress (compressBlocks hash a) (NIST.Encoding.octetsToBits (filledBlock a b)) := by
  rw [compressBlocks_append_buffered]
  exact compressBlocks_single _ _ (filledBlock_size a b h)

theorem filled_prefix_counts (a b : ByteArray) (h : 64-a.size%64 ≤ b.size) :
    (a ++ b.extract 0 (64-a.size%64)).size%64 = 0 ∧
    (a ++ b.extract 0 (64-a.size%64)).size/64 = a.size/64+1 := by
  rw [ByteArray.size_append,ByteArray.size_extract,Nat.min_eq_left h,Nat.sub_zero]
  omega

end Hkdf.Proofs.Wrapper.Absorb
