import Md5.Proofs.Buffered.Update.ResetFirst.ShortUpdate
import Md5.Proofs.Buffered.Update.ResetFirst.Aligned
import Md5.Proofs.Buffered.Update.ResetFirst.Filled
import Md5.Proofs.Buffered.Update.ResetFirst.Batch

namespace Md5.Proofs.Buffered

open X86 X86.Machine X86.UserProcess X86Proofs

theorem ResetFirst.update_of_kind [Bindings] {kind : UpdateKind} (hk : ResetFirst.KindSupported kind) {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) :
    ∃ t, UpdatePost kind boundary message input s t := by
  by_cases hshort : message.size % 64 + input.size < 64
  · exact ResetFirst.update_short_of_kind hk h hshort
  have hfull : 64 ≤ message.size % 64 + input.size := by omega
  by_cases hpos : message.size % 64 = 0
  · obtain ⟨u, hu⟩ := ResetFirst.aligned_ready_of_kind hk h hfull hpos
    obtain ⟨t, ht⟩ := ResetFirst.batch_run_of_kind hk h hu
    exact ⟨t, ht.toUpdatePost_aligned hpos⟩
  · obtain ⟨u, hu⟩ := ResetFirst.filled_ready_of_kind hk h hfull hpos
    obtain ⟨t, ht⟩ := ResetFirst.batch_run_of_kind hk h hu
    exact ⟨t, ht.toUpdatePost_fill (by omega)⟩


theorem update_resetFirst [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .resetFirst boundary message input s) :
    ∃ t, UpdatePost .resetFirst boundary message input s t := by
  exact ResetFirst.update_of_kind (kind := .resetFirst) (Or.inl rfl) h

theorem update_finalizeResetFirst [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .finalizeResetFirst boundary message input s) :
    ∃ t, UpdatePost .finalizeResetFirst boundary message input s t := by
  exact ResetFirst.update_of_kind (kind := .finalizeResetFirst) (Or.inr (Or.inl rfl)) h

theorem update_resetDiscardFirst [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .resetDiscardFirst boundary message input s) :
    ∃ t, UpdatePost .resetDiscardFirst boundary message input s t := by
  exact ResetFirst.update_of_kind (kind := .resetDiscardFirst) (Or.inr (Or.inr rfl)) h

end Md5.Proofs.Buffered
