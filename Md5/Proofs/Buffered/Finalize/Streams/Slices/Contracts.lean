import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Buffered.Finalize.Algebra

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure LengthReady [Bindings] (message : ByteArray) (s : RamState) (update : Bool := false) : Prop
    extends Storage (streamKind update) s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  rip : s.RIP = (BitVec.ofNat 64 (relocated update 0x10053d))
  prefixBytes : Bytes s.external (stackPtr s + 16) 56
    (fun i ↦ if message.size % 64 < 56 then (firstBlock message)[i]! else 0)
  buffer : (⟨(stackPtr s).toNat, 16⟩ : MemoryRegion).HasBytes s.external
    ⟨(paddedBuffer message).toBytes.toArray⟩
  blocks : (.reg 14 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64)
  position : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64)

structure CallReady [Bindings] (message : ByteArray) (s : RamState) (update : Bool := false) : Prop
    extends Storage (streamKind update) s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  rip : s.RIP = (BitVec.ofNat 64 (relocated update 0x1005b4))
  input : (⟨(stackPtr s).toNat + 104, 64⟩ : MemoryRegion).HasBytes s.external (lastBlock message)
  buffer : (⟨(stackPtr s).toNat, 16⟩ : MemoryRegion).HasBytes s.external
    ⟨(paddedBuffer message).toBytes.toArray⟩
  source : (.reg 6 : Operand 64).read s = stackPtr s + 104
  destination : (.reg 7 : Operand 64).read s = stackPtr s
  count : (.reg 2 : Operand 64).read s = 1

end Md5.Proofs.Buffered.Finalize.Streams.Slices
