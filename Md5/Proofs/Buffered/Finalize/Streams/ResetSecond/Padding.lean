import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding.Short
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding.Long

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond

open Md5.Spec.Program X86 X86.Machine X86.UserProcess

theorem pad [Bindings] {variant : Variant} {boundary : ReturnBoundary} {message : ByteArray} {s : RamState}
    (hOutside : ¬ InProgram boundary.rip) (h : Prepared message s variant) :
    ∃ t, Transition boundary s t variant ∧ Padded message t variant := by
  by_cases hshort : message.size % 64 < 56
  · exact Padding.short hOutside h hshort
  · exact Padding.long hOutside h hshort

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond
