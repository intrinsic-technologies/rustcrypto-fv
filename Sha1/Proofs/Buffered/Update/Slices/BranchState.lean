import Sha1.Proofs.Buffered.Update.Contracts

namespace Sha1.Proofs.Buffered.Update.Slices

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure BranchState [Bindings] (boundary : ReturnBoundary) (message input : ByteArray)
    (s u : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s u
  ready : ReadyToStep u
  code : CodeIn Extracted.programImage u
  rip : u.RIP = if input.size < 64 - message.size % 64 then 0x101cb0 else 0x101d0e
  position : (Operand.reg 13 : Operand 64).read u = BitVec.ofNat 64 (message.size % 64)
  gap : (Operand.reg 2 : Operand 64).read u = BitVec.ofNat 64 (64 - message.size % 64)
  remaining : (Operand.reg 5 : Operand 64).read u =
    BitVec.ofNat 64 input.size - BitVec.ofNat 64 (64 - message.size % 64)
  agrees : AgreesExcept [.reg 13, .reg 2, .reg 5, .flags, .rip] s u

end Sha1.Proofs.Buffered.Update.Slices
