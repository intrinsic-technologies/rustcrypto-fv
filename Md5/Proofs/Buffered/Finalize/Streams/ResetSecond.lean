import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Finish

namespace Md5.Proofs.Buffered.Finalize

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem Streams.ResetSecond.finalize [Bindings] {variant : Streams.ResetSecond.Variant} {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre variant.toKind boundary message s) :
    ∃ t, Post variant.toKind boundary message s t := by
  obtain ⟨u, hsu, hu⟩ := Streams.ResetSecond.prepare hp
  obtain ⟨v, huv, hv⟩ := Streams.ResetSecond.pad hp.boundaryOutside hu
  obtain ⟨t, ht⟩ := Streams.ResetSecond.finish hp.boundaryOutside hv
  have hsv := hsu.trans huv
  have hvt : Streams.ResetSecond.Transition boundary v t variant := ⟨ht.advances, ht.agrees⟩
  have hst := hsv.trans hvt
  refine ⟨t, hst.advances, ht.ready, ht.code, ht.rip, ?_, hst.agrees⟩
  simpa only [Kind.resultRegion, hsv.rsp] using ht.digest

theorem resetSecond_finalize [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre .resetSecond boundary message s) :
    ∃ t, Post .resetSecond boundary message s t :=
  Streams.ResetSecond.finalize (variant := .original) hp

theorem finalizeResetSecond_finalize [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre .finalizeResetSecond boundary message s) :
    ∃ t, Post .finalizeResetSecond boundary message s t :=
  Streams.ResetSecond.finalize (variant := .finalize) hp

theorem resetDiscardSecond_finalize [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre .resetDiscardSecond boundary message s) :
    ∃ t, Post .resetDiscardSecond boundary message s t :=
  Streams.ResetSecond.finalize (variant := .discard) hp

end Md5.Proofs.Buffered.Finalize
