import Md5.Proofs.Buffered.Update.ResetSecond.Full.Blocks
import Md5.Proofs.Buffered.Update.ResetSecond.Tail

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec X86 X86.Machine X86.UserProcess X86Proofs

theorem batch_done [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset count : Nat} {buffer : Standards.RFC.MD5.Buffer}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s)
    (hu : UpdateBatchReady kind boundary input s offset buffer count u) :
    ∃ t, UpdateBatchDone kind boundary input s offset buffer count t := by
  obtain ⟨v, hv⟩ := blocks_done hkind h hu
  exact tail_done hkind h hv

end Md5.Proofs.Buffered.ResetSecond
