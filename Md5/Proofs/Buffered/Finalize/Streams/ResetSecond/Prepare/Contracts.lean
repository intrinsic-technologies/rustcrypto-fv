import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Contracts

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Prefix [Bindings] (message : ByteArray) (s : RamState) (variant : Variant := .original) : Prop
    extends Storage variant.toKind s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  rip : s.RIP = match variant with
    | .original => 0x100acf | .finalize => 0x10115f | .discard => 0x10163c
  absorbed : Absorbed (stackPtr s + BitVec.ofNat 64 variant.tailOffset) message s
  buffer : (⟨(stackPtr s).toNat + variant.resultOffset, 16⟩ : MemoryRegion).HasBytes s.external
    ⟨(absorbedBuffer message).toBytes.toArray⟩
  blocks : (Operand.reg 14 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64)
  position : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64)
  df : DirectionFlagClear s.RFLAGS

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
