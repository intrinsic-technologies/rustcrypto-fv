import Md5.Proofs.Buffered.Finalize.Streams.Slices.Long
import Md5.Proofs.Buffered.Finalize.Streams.Slices.FinalBlock

namespace Md5.Proofs.Buffered.Finalize

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem Streams.Slices.finalize {update : Bool} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre (Streams.Slices.streamKind update) boundary message s) :
    ∃ t, Post (Streams.Slices.streamKind update) boundary message s t := by
  obtain ⟨u, hu⟩ := Streams.Slices.pad (update := update) hp
  obtain ⟨v, hsv, hv⟩ := Streams.Slices.branch hp.boundaryOutside hu
  obtain ⟨w, hsw, hw⟩ : ∃ w, Streams.Slices.Transition (update := update) boundary s w ∧
      Streams.Slices.LengthReady (update := update) message w := by
    by_cases hShort : message.size % 64 < 56
    · exact ⟨v, hsv, hv.short hShort⟩
    · obtain ⟨w, hvw, hw⟩ := hv.long hp.boundaryOutside hShort
      exact ⟨w, hsv.trans hvw, hw⟩
  obtain ⟨x, hwx, hx⟩ := Streams.Slices.prepare_lastBlock hp.boundaryOutside hw
  obtain ⟨t, ht⟩ := Streams.Slices.Compression.finish hp.boundaryOutside hx
  have hsx := hsw.trans hwx
  have hst := hsx.trans ⟨ht.advances, ht.agrees⟩
  refine ⟨t, hst.advances, ht.ready, ht.code, ht.rip, ?_, hst.agrees⟩
  simpa only [Kind.resultRegion, hsx.rsp] using ht.digest

theorem slices_finalize [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre .slices boundary message s) :
    ∃ t, Post .slices boundary message s t :=
  Streams.Slices.finalize (update := false) hp

theorem updateFinalizeInto_finalize [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre .updateFinalizeInto boundary message s) :
    ∃ t, Post .updateFinalizeInto boundary message s t :=
  Streams.Slices.finalize (update := true) hp

end Md5.Proofs.Buffered.Finalize
