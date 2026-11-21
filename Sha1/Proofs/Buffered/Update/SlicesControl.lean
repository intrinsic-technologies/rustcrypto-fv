import Sha1.Proofs.Buffered.Update.Contracts

namespace Sha1.Proofs.Buffered.Update

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem position_eq [bindings : Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .updateFinalize boundary message input s) :
    (Operand.mem (stackPtr s + 0x117) : Operand 8).read s =
      BitVec.ofNat 8 (message.size % 64) := by
  simpa only [UpdateKind.context, UpdateKind.contextOffset, size_tailBytes, BitVec.add_assoc,
    show (BitVec.ofNat 64 0xd8 + 63) = 0x117 by decide] using h.absorbed.position

theorem inputSize_lt [bindings : Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .updateFinalize boundary message input s) : input.size < 2^32 := by
  have hi := h.inputBounded
  change ((Operand.reg (UpdateKind.updateFinalize).inputRegister : Operand 64).read s).toNat +
    input.size < 2^32 at hi
  simp only [UpdateKind.inputRegister] at hi
  omega

end Sha1.Proofs.Buffered.Update
