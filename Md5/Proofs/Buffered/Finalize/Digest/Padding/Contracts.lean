import Md5.Proofs.Buffered.Finalize.Digest.Padding.Fill

namespace Md5.Proofs.Buffered.Finalize.Digest.Padding

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Input [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s : RamState) : Prop extends RunPre s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  boundaryOutside : ¬ InProgram boundary.rip
  df : DirectionFlagClear s.RFLAGS
  positionEq : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64)
  remainingEq : (Operand.reg 14 : Operand 64).read s = BitVec.ofNat 64 (63 - message.size % 64)
  blocksEq : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64)
  tail : (⟨(stackPtr s + 24).toNat, (tailBytes message).size⟩ : MemoryRegion).HasBytes
    s.external (tailBytes message)
  buffer : (⟨(stackPtr s + 8).toNat, 16⟩ : MemoryRegion).HasBytes
    s.external ⟨(absorbedBuffer message).toBytes.toArray⟩

structure Result [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = 0x100120
  storage : Storage .digest t
  rsp : stackPtr t = stackPtr s
  position : (Operand.reg 12 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64)
  remaining : (Operand.reg 14 : Operand 64).read t = BitVec.ofNat 64 (63 - message.size % 64)
  blocks : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64)
  padded : Bytes t.external (stackPtr t + 24) 64 (fun i ↦ (firstBlock message)[i]!)
  buffer : (⟨(stackPtr t + 8).toNat, 16⟩ : MemoryRegion).HasBytes
    t.external ⟨(absorbedBuffer message).toBytes.toArray⟩
  agrees : AgreesExcept (Kind.digest.changes s) s t

end Md5.Proofs.Buffered.Finalize.Digest.Padding
