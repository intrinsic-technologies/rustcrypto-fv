import Standards.NIST.SHA2
import Sha1.Spec
import Sha1.Proofs.Compress.Parser

set_option autoImplicit false

namespace Sha1.Proofs.Wrapper.Absorb

open Standards.NIST Standards.NIST.SHA2
open Sha1.Spec.Program


def fullBlocks (input : ByteArray) : ByteArray :=
  input.extract 0 (64 * (input.size / 64))


def remainderBytes (input : ByteArray) : ByteArray :=
  input.extract (64 * (input.size / 64)) input.size


def compressBlocks (hash : Vector (BitVec 32) 5) (input : ByteArray) :
    Vector (BitVec 32) 5 :=
  (SHA256.parse (bytesToBits input)).foldl SHA1.compress hash

theorem fullBlocks_size (input : ByteArray) :
    (fullBlocks input).size = 64 * (input.size / 64) := by
  simp only [fullBlocks, ByteArray.size_extract, Nat.sub_zero]
  exact Nat.min_eq_left (by omega)

theorem remainderBytes_size (input : ByteArray) :
    (remainderBytes input).size = input.size % 64 := by
  simp only [remainderBytes, ByteArray.size_extract, Nat.min_self]
  omega

theorem fullBlocks_append_remainderBytes (input : ByteArray) :
    fullBlocks input ++ remainderBytes input = input := by
  rw [fullBlocks, remainderBytes, ByteArray.extract_append_extract,
    Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right
      (show 64 * (input.size / 64) ≤ input.size by omega),
    ByteArray.extract_zero_size]

theorem compressBlocks_append (hash : Vector (BitVec 32) 5) (a b : ByteArray)
    (ha : a.size % 64 = 0) :
    compressBlocks hash (a ++ b) = compressBlocks (compressBlocks hash a) b := by
  unfold compressBlocks
  rw [Sha1.Proofs.Compress.Parser.parse_append a b ha, Array.foldl_append]

theorem remainderBytes_append_aligned (a b : ByteArray)
    (ha : a.size % 64 = 0) :
    remainderBytes (a ++ b) = remainderBytes b := by
  have hs : 64*((a.size+b.size)/64) = a.size+64*(b.size/64) := by omega
  simp only [remainderBytes, ByteArray.size_append, hs,
    ByteArray.extract_append_size_add]

theorem remainderBytes_append_buffered (a b : ByteArray) :
    remainderBytes (a ++ b) = remainderBytes (remainderBytes a ++ b) := by
  conv => lhs; rw [← fullBlocks_append_remainderBytes a, ByteArray.append_assoc]
  exact remainderBytes_append_aligned _ _ (by rw [fullBlocks_size]; omega)

theorem remainderBytes_short (input : ByteArray) (h : input.size < 64) :
    remainderBytes input = input := by
  simp only [remainderBytes, Nat.div_eq_of_lt h, Nat.mul_zero,
    ByteArray.extract_zero_size]

theorem remainderBytes_append_short (a b : ByteArray)
    (h : b.size < 64 - a.size % 64) :
    remainderBytes (a ++ b) = remainderBytes a ++ b := by
  rw [remainderBytes_append_buffered, remainderBytes_short]
  rw [ByteArray.size_append, remainderBytes_size]
  omega

def filledBlock (a b : ByteArray) : ByteArray :=
  remainderBytes a ++ b.extract 0 (64 - a.size % 64)

def afterFilledBlock (a b : ByteArray) : ByteArray :=
  b.extract (64 - a.size % 64) b.size

theorem filledBlock_size (a b : ByteArray)
    (h : 64 - a.size % 64 ≤ b.size) :
    (filledBlock a b).size = 64 := by
  simp only [filledBlock, ByteArray.size_append, remainderBytes_size,
    ByteArray.size_extract, Nat.min_eq_left h, Nat.sub_zero]
  omega

theorem filledBlock_append_after (a b : ByteArray) :
    filledBlock a b ++ afterFilledBlock a b = remainderBytes a ++ b := by
  simp only [filledBlock, afterFilledBlock, ByteArray.append_assoc]
  congr 1
  rw [ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
    ByteArray.extract_zero_max_size]

theorem afterFilledBlock_size (a b : ByteArray) :
    (afterFilledBlock a b).size = b.size - (64 - a.size % 64) := by
  simp only [afterFilledBlock, ByteArray.size_extract, Nat.min_self]

theorem append_short_counts (a b : ByteArray)
    (h : b.size < 64 - a.size % 64) :
    (a ++ b).size / 64 = a.size / 64 ∧
      (a ++ b).size % 64 = a.size % 64 + b.size := by
  rw [ByteArray.size_append]
  omega

theorem append_filled_counts (a b : ByteArray)
    (h : 64 - a.size % 64 ≤ b.size) :
    (a ++ b).size / 64 = a.size / 64 + 1 + (afterFilledBlock a b).size / 64 ∧
      (a ++ b).size % 64 = (afterFilledBlock a b).size % 64 := by
  rw [ByteArray.size_append, afterFilledBlock_size]
  omega

theorem filled_prefix_counts (a b : ByteArray)
    (h : 64-a.size%64 ≤ b.size) :
    (a ++ b.extract 0 (64-a.size%64)).size%64 = 0 ∧
    (a ++ b.extract 0 (64-a.size%64)).size/64 = a.size/64+1 := by
  rw [ByteArray.size_append, ByteArray.size_extract, Nat.min_eq_left h, Nat.sub_zero]
  omega

end Sha1.Proofs.Wrapper.Absorb
