import Sha1.Spec
import Sha1.Proofs.Wrapper.Absorb.Mathematics
import Sha1.Proofs.Wrapper.Hash.Serialize
import Sha1.Proofs.Compress.StateMemory
import X86Proofs.Program.ReadWrite.Bytes

namespace Sha1.Proofs.Buffered

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Spec Sha1.Spec.Program
open Sha1.Proofs.Wrapper.Absorb
open Standards.NIST Standards.NIST.SHA1 Standards.NIST.SHA2


def fullBytes (message : ByteArray) : ByteArray :=
  fullBlocks message


def tailBytes (message : ByteArray) : ByteArray :=
  remainderBytes message


def absorbedHash (message : ByteArray) : Vector (BitVec 32) 5 :=
  compressBlocks SHA1.initialHashValue (fullBytes message)


def absorbedStateBytes (message : ByteArray) : ByteArray :=
  Sha1.Proofs.Wrapper.Hash.Serialize.stateBytes (absorbedHash message)


structure Absorbed (base : BitVec 64) (message : ByteArray) (s : Machine.RamState) : Prop where
  state : (⟨(base + 72).toNat, 20⟩ : MemoryRegion).HasBytes s.external
    (absorbedStateBytes message)
  tail : (⟨base.toNat, (tailBytes message).size⟩ : MemoryRegion).HasBytes
    s.external (tailBytes message)
  position : (Operand.mem (base + 63) : Operand 8).read s =
    BitVec.ofNat 8 (tailBytes message).size
  blocks : (Operand.mem (base + 64) : Operand 64).read s =
    BitVec.ofNat 64 (message.size / 64)

@[simp] theorem size_fullBytes (message : ByteArray) :
    (fullBytes message).size = 64 * (message.size / 64) := by
  exact fullBlocks_size message

@[simp] theorem size_tailBytes (message : ByteArray) :
    (tailBytes message).size = message.size % 64 := by
  exact remainderBytes_size message

theorem fullBytes_append_tailBytes (message : ByteArray) :
    fullBytes message ++ tailBytes message = message := by
  exact fullBlocks_append_remainderBytes message

theorem fullBytes_aligned (message : ByteArray) :
    (fullBytes message).size % 64 = 0 := by
  rw [size_fullBytes]
  omega

theorem tailBytes_lt (message : ByteArray) :
    (tailBytes message).size < 64 := by
  rw [size_tailBytes]
  omega

theorem absorbedHash_empty : absorbedHash ByteArray.empty = SHA1.initialHashValue := by
  unfold absorbedHash fullBytes
  simp only [fullBlocks, ByteArray.size_empty, Nat.zero_div, Nat.mul_zero]
  unfold compressBlocks
  change Array.foldl SHA1.compress SHA1.initialHashValue
    (SHA2.SHA256.parse (SHA2.bytesToBits ByteArray.empty)) = SHA1.initialHashValue
  rw [Sha1.Proofs.Compress.Parser.parse_empty]
  rfl

theorem absorbedStateBytes_size (message : ByteArray) :
    (absorbedStateBytes message).size = 20 := by
  exact Sha1.Proofs.Wrapper.Hash.Serialize.stateBytes_size _

theorem absorbedHash_append_aligned (hash : Vector (BitVec 32) 5)
    (a b : ByteArray) (ha : a.size % 64 = 0) :
    compressBlocks hash (a ++ b) = compressBlocks (compressBlocks hash a) b := by
  exact compressBlocks_append hash a b ha

theorem absorbedHash_message (message : ByteArray) :
    absorbedHash message =
      (SHA2.SHA256.parse (SHA2.bytesToBits (fullBytes message))).foldl SHA1.compress
        SHA1.initialHashValue := by
  rfl

end Sha1.Proofs.Buffered
