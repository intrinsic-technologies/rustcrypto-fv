import Md5.Proofs.Buffered.Update.Slices.Short.Result
import Md5.Proofs.Buffered.Update.Slices.Full

namespace Md5.Proofs.Buffered

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem Update.Slices.update [Bindings] {variant : Bool} {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre (Update.Slices.kind variant) boundary message input s) :
    ∃ t, UpdatePost (Update.Slices.kind variant) boundary message input s t := by
  by_cases hshort : message.size % 64 + input.size < 64
  · exact Update.Slices.update_short h hshort
  · obtain ⟨u, hp⟩ := Update.Slices.prepare h
    exact Update.Slices.full h hp (by omega)

theorem update_slices [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .slices boundary message input s) :
    ∃ t, UpdatePost .slices boundary message input s t :=
  Update.Slices.update (variant := false) h

theorem update_finalizeInto [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .updateFinalizeInto boundary message input s) :
    ∃ t, UpdatePost .updateFinalizeInto boundary message input s t :=
  Update.Slices.update (variant := true) h

end Md5.Proofs.Buffered
