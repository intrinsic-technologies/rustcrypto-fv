import Sha1.Proofs.Buffered.Update.Slices.Full.Filled.Compress

namespace Sha1.Proofs.Buffered.Update.Slices.Full

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem filled [Bindings] {boundary : ReturnBoundary} {message input : ByteArray} {s u : RamState}
    (h : UpdatePre .updateFinalize boundary message input s)
    (b : BranchState boundary message input s u)
    (hsize : 64 - message.size % 64 ≤ input.size) (hpos : message.size % 64 ≠ 0) :
    ∃ v, BatchReady boundary message input s (64 - message.size % 64) v := by
  obtain ⟨v, hv⟩ := Filled.copy_entry h b hsize hpos
  obtain ⟨w, hw⟩ := Filled.compress_copied h hv hsize
  exact Filled.resume h hw hsize

end Sha1.Proofs.Buffered.Update.Slices.Full
