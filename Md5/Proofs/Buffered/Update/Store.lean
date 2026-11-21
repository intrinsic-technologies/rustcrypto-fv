import Md5.Proofs.Buffered.Update.Memory
import Md5.Proofs.Block.Entry

namespace Md5.Proofs.Buffered

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem UpdatePre.contextStorePre [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s t : RamState}
    (h : UpdatePre kind boundary message input s) {changes : List Component}
    (ha : AgreesExcept changes s t) (hsp : stackPtr t = stackPtr s)
    {p : BitVec 64} (hrip : t.RIP = p) (len i n : Nat) (hi : i + n ≤ 88)
    (htext : ∀ j < len, InProgram (p + BitVec.ofNat 64 j)) :
    Memory.StorePre p len
      (fun u ↦ stackPtr u + BitVec.ofNat 64 (kind.contextOffset + i)) n t := by
  have hw := h.contextWritable_of_agrees ha i n hi
  refine ⟨hrip, ?_, ?_⟩
  · rw [hsp]
    exact ⟨hw.readable.low, hw.readable.mem, hw.tables⟩
  · intro j hj k hk he
    rw [hsp] at he
    exact hw.code j hj (he ▸ htext k hk)

end Md5.Proofs.Buffered
