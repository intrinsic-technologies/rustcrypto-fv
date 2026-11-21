import Md5.Proofs.Buffered.Update.ResetSecond.Short
import Md5.Proofs.Buffered.Update.ResetSecond.Full

namespace Md5.Proofs.Buffered

open X86 X86.Machine X86.UserProcess X86Proofs

theorem ResetSecond.update [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s) :
    ∃ t, UpdatePost kind boundary message input s t := by
  by_cases hshort : message.size % 64 + input.size < 64
  · exact ResetSecond.short_update hkind h hshort
  · exact ResetSecond.full_update hkind h (by omega)

theorem update_resetSecond [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .resetSecond boundary message input s) :
    ∃ t, UpdatePost .resetSecond boundary message input s t :=
  ResetSecond.update (Or.inl rfl) h

theorem update_finalizeResetSecond [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .finalizeResetSecond boundary message input s) :
    ∃ t, UpdatePost .finalizeResetSecond boundary message input s t :=
  ResetSecond.update (Or.inr (Or.inl rfl)) h

theorem update_resetDiscardSecond [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .resetDiscardSecond boundary message input s) :
    ∃ t, UpdatePost .resetDiscardSecond boundary message input s t :=
  ResetSecond.update (Or.inr (Or.inr rfl)) h

end Md5.Proofs.Buffered
