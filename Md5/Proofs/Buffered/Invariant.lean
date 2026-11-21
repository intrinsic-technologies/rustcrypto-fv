import Md5.Proofs.Machine
import Md5.Proofs.RFC1321.Processing
import Init.Data.ByteArray.Lemmas

namespace Md5.Proofs.Buffered

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86Proofs

def fullBytes (message : ByteArray) : ByteArray :=
  message.extract 0 (message.size / 64 * 64)

def tailBytes (message : ByteArray) : ByteArray :=
  message.extract (message.size / 64 * 64) message.size

def absorbedBuffer (message : ByteArray) : Standards.RFC.MD5.Buffer :=
  Standards.RFC.MD5.processBlocks Standards.RFC.MD5.Buffer.initial
    (Standards.RFC.MD5.wordsOfBytes (fullBytes message))

structure Absorbed (context : BitVec 64) (message : ByteArray) (s : RamState) : Prop where
  buffer : (⟨context.toNat + 64, 16⟩ : MemoryRegion).HasBytes s.external
    ⟨(absorbedBuffer message).toBytes.toArray⟩
  tail : (⟨context.toNat, (tailBytes message).size⟩ : MemoryRegion).HasBytes
    s.external (tailBytes message)
  position : (Operand.mem (context + 63) : Operand 8).read s =
    BitVec.ofNat 8 (message.size % 64)
  blocks : (Operand.mem (context + 80) : Operand 64).read s =
    BitVec.ofNat 64 (message.size / 64)

theorem size_fullBytes (message : ByteArray) :
    (fullBytes message).size = message.size / 64 * 64 := by
  simp only [fullBytes, ByteArray.size_extract]
  omega

theorem size_tailBytes (message : ByteArray) :
    (tailBytes message).size = message.size % 64 := by
  simp only [tailBytes, ByteArray.size_extract]
  omega

theorem fullBytes_append_tailBytes (message : ByteArray) :
    fullBytes message ++ tailBytes message = message := by
  simp only [fullBytes, tailBytes, ByteArray.extract_append_extract, Nat.zero_min,
    Nat.max_eq_right (Nat.div_mul_le_self ..), ByteArray.extract_zero_size]

theorem fullBytes_aligned (message : ByteArray) : (fullBytes message).size % 64 = 0 := by
  rw [size_fullBytes]
  omega

theorem tailBytes_lt (message : ByteArray) : (tailBytes message).size < 64 := by
  rw [size_tailBytes]
  omega

theorem absorbedBuffer_empty : absorbedBuffer ByteArray.empty = Standards.RFC.MD5.Buffer.initial := by
  exact RFC1321.processBlocks_empty _

end Md5.Proofs.Buffered
