import Md5.Proofs.Buffered.Update.Contracts
import Md5.Proofs.Buffered.Update.Algebra

namespace Md5.Proofs.Buffered

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

namespace UpdateKind

def batchSizeRegister : UpdateKind → BitVec 5
  | .slices => 5
  | .resetFirst => 3
  | .resetSecond => 14
  | .updateFinalizeInto => 5
  | .finalizeResetFirst => 3
  | .finalizeResetSecond => 14
  | .resetDiscardFirst => 13
  | .resetDiscardSecond => 14

def batchEntry : UpdateKind → BitVec 64
  | .slices => 0x1003c5
  | .resetFirst => 0x10072e
  | .resetSecond => 0x100a35
  | .updateFinalizeInto => 0x101975
  | .finalizeResetFirst => 0x100dde
  | .finalizeResetSecond => 0x1010c5
  | .resetDiscardFirst => 0x101467
  | .resetDiscardSecond => 0x1015a3

def tailEntry : UpdateKind → BitVec 64
  | .slices => 0x1003dd
  | .resetFirst => 0x100740
  | .resetSecond => 0x100a4a
  | .updateFinalizeInto => 0x10198d
  | .finalizeResetFirst => 0x100df0
  | .finalizeResetSecond => 0x1010da
  | .resetDiscardFirst => 0x101479
  | .resetDiscardSecond => 0x1015b5

def batchExit : UpdateKind → BitVec 64
  | .slices => 0x10040f
  | .resetFirst => 0x10076b
  | .resetSecond => 0x100a6f
  | .updateFinalizeInto => 0x1019bf
  | .finalizeResetFirst => 0x100e1b
  | .finalizeResetSecond => 0x1010ff
  | .resetDiscardFirst => 0x1014a6
  | .resetDiscardSecond => 0x1015df

end UpdateKind

structure UpdateBatchReady [Bindings] (kind : UpdateKind) (boundary : ReturnBoundary) (input : ByteArray)
    (s : RamState) (offset : Nat) (buffer : Standards.RFC.MD5.Buffer) (count : Nat) (u : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s u
  ready : ReadyToStep u
  code : CodeIn Extracted.programImage u
  rip : u.RIP = if (input.size - offset) / 64 = 0 then kind.tailEntry else kind.batchEntry
  agrees : AgreesExcept (kind.changes s) s u
  offsetBound : offset ≤ input.size
  pointer : (Operand.reg kind.inputRegister : Operand 64).read u =
    (Operand.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 offset
  size : (Operand.reg kind.batchSizeRegister : Operand 64).read u = BitVec.ofNat 64 (input.size - offset)
  blockCount : (Operand.reg 2 : Operand 64).read u = BitVec.ofNat 64 ((input.size - offset) / 64)
  bufferBytes : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
    u.external ⟨buffer.toBytes.toArray⟩
  counter : (Operand.mem (kind.context s + 80) : Operand 64).read u =
    BitVec.ofNat 64 count

structure UpdateBlocksDone [Bindings] (kind : UpdateKind) (boundary : ReturnBoundary) (input : ByteArray)
    (s : RamState) (offset : Nat) (buffer : Standards.RFC.MD5.Buffer) (count : Nat) (u : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s u
  ready : ReadyToStep u
  code : CodeIn Extracted.programImage u
  rip : u.RIP = kind.tailEntry
  agrees : AgreesExcept (kind.changes s) s u
  offsetBound : offset ≤ input.size
  pointer : (Operand.reg kind.inputRegister : Operand 64).read u =
    (Operand.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 offset
  size : (Operand.reg kind.batchSizeRegister : Operand 64).read u = BitVec.ofNat 64 (input.size - offset)
  bufferBytes : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
    u.external ⟨(Standards.RFC.MD5.processBlocks buffer
      (Standards.RFC.MD5.wordsOfBytes (fullBytes (input.extract offset input.size)))).toBytes.toArray⟩
  counter : (Operand.mem (kind.context s + 80) : Operand 64).read u =
    BitVec.ofNat 64 (count + (input.size - offset) / 64)

structure UpdateBatchDone [Bindings] (kind : UpdateKind) (boundary : ReturnBoundary) (input : ByteArray)
    (s : RamState) (offset : Nat) (buffer : Standards.RFC.MD5.Buffer) (count : Nat) (t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = kind.batchExit
  agrees : AgreesExcept (kind.changes s) s t
  bufferBytes : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
    t.external ⟨(Standards.RFC.MD5.processBlocks buffer
      (Standards.RFC.MD5.wordsOfBytes (fullBytes (input.extract offset input.size)))).toBytes.toArray⟩
  tail : (⟨(kind.context s).toNat,
      (tailBytes (input.extract offset input.size)).size⟩ : MemoryRegion).HasBytes
    t.external (tailBytes (input.extract offset input.size))
  position : (Operand.mem (kind.context s + 63) : Operand 8).read t =
    BitVec.ofNat 8 ((input.size - offset) % 64)
  counter : (Operand.mem (kind.context s + 80) : Operand 64).read t =
    BitVec.ofNat 64 (count + (input.size - offset) / 64)

theorem UpdateBatchDone.toUpdatePost_aligned [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s t : RamState}
    (h : UpdateBatchDone kind boundary input s 0 (absorbedBuffer message) (message.size / 64) t)
    (hpos : message.size % 64 = 0) : UpdatePost kind boundary message input s t := by
  refine ⟨h.advances, h.ready, h.code, ?_, ?_, h.agrees⟩
  · rw [h.rip]
    cases kind <;> decide
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [absorbedBuffer_append_aligned message input hpos]
      simpa only [ByteArray.extract_zero_size] using h.bufferBytes
    · rw [tailBytes_append, tailBytes_of_aligned message hpos, ByteArray.empty_append]
      simpa only [ByteArray.extract_zero_size] using h.tail
    · rw [position_append_aligned message input hpos]
      simpa only [Nat.sub_zero] using h.position
    · rw [blockCount_append_aligned message input hpos]
      simpa only [Nat.sub_zero] using h.counter

theorem UpdateBatchDone.toUpdatePost_fill [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s t : RamState}
    (h : UpdateBatchDone kind boundary input s (64 - message.size % 64)
      (Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (updateBlock message input))) (message.size / 64 + 1) t)
    (hfull : 64 - message.size % 64 ≤ input.size) : UpdatePost kind boundary message input s t := by
  refine ⟨h.advances, h.ready, h.code, ?_, ?_, h.agrees⟩
  · rw [h.rip]
    cases kind <;> decide
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [absorbedBuffer_append_fill message input hfull]
      exact h.bufferBytes
    · rw [tailBytes_append_fill message input hfull]
      exact h.tail
    · rw [position_append_fill message input hfull, size_updateRemainder]
      exact h.position
    · rw [blockCount_append_fill message input hfull, size_updateRemainder]
      exact h.counter

theorem UpdateBatchReady.noBlocks [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {input : ByteArray} {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (h : UpdateBatchReady kind boundary input s offset buffer count u)
    (hz : (input.size - offset) / 64 = 0) :
    UpdateBlocksDone kind boundary input s offset buffer count u := by
  have he : fullBytes (input.extract offset input.size) = ByteArray.empty := by
    apply fullBytes_of_size_lt
    simp only [ByteArray.size_extract, Nat.min_self]
    omega
  refine ⟨h.advances, h.ready, h.code, ?_, h.agrees, h.offsetBound, h.pointer, h.size, ?_, ?_⟩
  · simpa only [hz, ite_true] using h.rip
  · rw [he]
    change (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes u.external
      ⟨(Standards.RFC.MD5.processBlocks buffer #[]).toBytes.toArray⟩
    rw [RFC1321.processBlocks_empty]
    exact h.bufferBytes
  · simpa only [hz, Nat.add_zero] using h.counter

end Md5.Proofs.Buffered
