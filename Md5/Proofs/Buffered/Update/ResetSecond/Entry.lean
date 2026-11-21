import Md5.Proofs.Buffered.Update.ResetSecond.Control
import Md5.Proofs.Buffered.Update.Memory

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

theorem position_of_pre [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) :
    position kind s = BitVec.ofNat 64 (message.size % 64) := by
  rw [position, h.absorbed.position]
  apply BitVec.setWidth_ofNat_of_le_of_lt (by decide)
  omega

theorem capacity_of_pre [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) :
    64 - position kind s = BitVec.ofNat 64 (64 - message.size % 64) := by
  rw [position_of_pre h]
  exact BitVec.ofNat_sub_ofNat_of_le 64 (message.size % 64) (by omega) (by omega)

theorem short_condition_iff [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) :
    ((.reg kind.sizeRegister : Operand 64).read s).toNat < (64 - position kind s).toNat ↔
      message.size % 64 + input.size < 64 := by
  have hs : (.reg kind.sizeRegister : Operand 64).read s = BitVec.ofNat 64 input.size := h.inputSize
  rw [hs, capacity_of_pre h]
  simp only [BitVec.toNat_ofNat]
  have ht := h.totalSize
  rw [Nat.mod_eq_of_lt (show input.size < 2^64 by omega),
    Nat.mod_eq_of_lt (show 64 - message.size % 64 < 2^64 by omega)]
  omega

end Md5.Proofs.Buffered.ResetSecond
