import Md5.Proofs.Buffered.Update.ResetSecond.Full.Aligned
import Md5.Proofs.Buffered.Update.ResetSecond.Full.Fill
import Md5.Proofs.Buffered.Update.ResetSecond.Full.Batch

namespace Md5.Proofs.Buffered.ResetSecond

open X86 X86.Machine X86.UserProcess X86Proofs

theorem full_update [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) :
    ∃ t, UpdatePost kind boundary message input s t := by
  by_cases hpos : message.size % 64 = 0
  · obtain ⟨u, hu⟩ := aligned_ready hkind h hfull hpos
    obtain ⟨t, ht⟩ := batch_done hkind h hu
    exact ⟨t, ht.toUpdatePost_aligned hpos⟩
  · obtain ⟨u, hu⟩ := filled_ready hkind h hfull hpos
    obtain ⟨t, ht⟩ := batch_done hkind h hu
    exact ⟨t, ht.toUpdatePost_fill (by omega)⟩

end Md5.Proofs.Buffered.ResetSecond
