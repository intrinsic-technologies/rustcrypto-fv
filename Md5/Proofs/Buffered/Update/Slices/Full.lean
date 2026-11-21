import Md5.Proofs.Buffered.Update.Slices.Full.Prepare
import Md5.Proofs.Buffered.Update.Slices.Full.Batch

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem full {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre (kind variant) boundary message input s)
    (hp : Prepared variant boundary s u) (hfull : 64 - message.size % 64 ≤ input.size) :
    ∃ t, UpdatePost (kind variant) boundary message input s t := by
  by_cases hpos : message.size % 64 = 0
  · obtain ⟨v, hv⟩ := aligned_ready h hp hfull hpos
    obtain ⟨t, ht⟩ := batch h hv
    exact ⟨t, ht.toUpdatePost_aligned hpos⟩
  · obtain ⟨v, hv⟩ := filled_ready h hp hfull hpos
    obtain ⟨t, ht⟩ := batch h hv
    exact ⟨t, ht.toUpdatePost_fill hfull⟩

end Md5.Proofs.Buffered.Update.Slices
