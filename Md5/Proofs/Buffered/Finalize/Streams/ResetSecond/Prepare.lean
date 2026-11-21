import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.Prefix
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare.Complete

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare [Bindings] {variant : Variant} {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Finalize.Pre variant.toKind boundary message s) :
    ∃ t, Transition boundary s t variant ∧ Prepared message t variant := by
  obtain ⟨u, hsu, hu⟩ := Prepare.prefix h
  obtain ⟨t, hut, ht⟩ := Prepare.complete hu h.stride h.boundaryOutside
  exact ⟨t, hsu.trans hut, ht⟩

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond
