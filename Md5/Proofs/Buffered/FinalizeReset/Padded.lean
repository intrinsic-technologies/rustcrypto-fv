import Md5.Proofs.Buffered.FinalizeReset.Contracts
import Md5.Proofs.Buffered.Finalize.Algebra
import Md5.Proofs.Block.Bytes

namespace Md5.Proofs.Buffered.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Padded [Bindings] (message : ByteArray) (s : RamState) (variant : Variant := .saved) : Prop extends Storage s variant where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  rip : s.RIP = (variant.address 0x1008a2)
  position : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64)
  bitBlocks : (Operand.reg 14 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64) <<< 9
  buffer : (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes s.external
    ⟨(Finalize.paddedBuffer message).toBytes.toArray⟩
  prefixBytes : Bytes s.external (stackPtr s + 8) 56
    (fun i ↦ if message.size % 64 < 56 then (Finalize.firstBlock message)[i]! else 0)

end Md5.Proofs.Buffered.FinalizeReset
