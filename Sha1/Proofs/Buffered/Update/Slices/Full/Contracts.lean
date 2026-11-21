import Sha1.Proofs.Buffered.Update.Slices.BranchState

namespace Sha1.Proofs.Buffered.Update.Slices.Full

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure BatchFrame [Bindings] (boundary : ReturnBoundary) (input : ByteArray)
    (s : RamState) (offset : Nat) (u : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s u
  ready : ReadyToStep u
  code : CodeIn Extracted.programImage u
  agrees : AgreesExcept (UpdateKind.updateFinalize.changes s) s u
  offsetBound : offset ≤ input.size
  pointer : (Operand.reg 14 : Operand 64).read u =
    (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 offset
  size : (Operand.reg 5 : Operand 64).read u = BitVec.ofNat 64 (input.size - offset)

structure BatchReady [Bindings] (boundary : ReturnBoundary) (message input : ByteArray)
    (s : RamState) (offset : Nat) (u : RamState) : Prop
    extends BatchFrame boundary input s offset u where
  rip : u.RIP = if (input.size - offset) / 64 = 0 then 0x101d7d else 0x101d65
  blockCount : (Operand.reg 2 : Operand 64).read u = BitVec.ofNat 64 ((input.size - offset) / 64)
  aligned : (message.size + offset) % 64 = 0
  state : (⟨(UpdateKind.updateFinalize.context s + 72).toNat, 20⟩ : MemoryRegion).HasBytes
    u.external (absorbedStateBytes (message ++ input.extract 0 offset))
  counter : (Operand.mem (UpdateKind.updateFinalize.context s + 64) : Operand 64).read u =
    BitVec.ofNat 64 ((message.size + offset) / 64)

structure TailReady [Bindings] (boundary : ReturnBoundary) (message input : ByteArray)
    (s : RamState) (offset : Nat) (u : RamState) : Prop
    extends BatchFrame boundary input s offset u where
  rip : u.RIP = 0x101d7d
  aligned : (message.size + offset) % 64 = 0
  state : (⟨(UpdateKind.updateFinalize.context s + 72).toNat, 20⟩ : MemoryRegion).HasBytes
    u.external (absorbedStateBytes (message ++ input))
  counter : (Operand.mem (UpdateKind.updateFinalize.context s + 64) : Operand 64).read u =
    BitVec.ofNat 64 ((message ++ input).size / 64)

end Sha1.Proofs.Buffered.Update.Slices.Full
