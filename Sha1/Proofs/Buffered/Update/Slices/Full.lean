import Sha1.Proofs.Buffered.Update.Slices.Full.Aligned
import Sha1.Proofs.Buffered.Update.Slices.Full.Filled
import Sha1.Proofs.Buffered.Update.Slices.Full.Batch
import Sha1.Proofs.Buffered.Update.Slices.Full.Tail

namespace Sha1.Proofs.Buffered.Update.Slices

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem full [bindings : Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre .updateFinalize boundary message input s)
    (b : BranchState boundary message input s u)
    (hsize : 64 - message.size % 64 ≤ input.size)
    (hInputNonzero : (UpdateKind.inputRegion .updateFinalize s input).start ≠ 0) :
    ∃ t, UpdatePost .updateFinalize boundary message input s t := by
  have prepare : ∃ offset v, Full.BatchReady boundary message input s offset v := by
    by_cases hpos : message.size % 64 = 0
    · exact ⟨0, Full.aligned h b hsize hpos⟩
    · exact ⟨_, Full.filled h b hsize hpos⟩
  obtain ⟨offset, v, hv⟩ := prepare
  obtain ⟨w, hw⟩ := Full.batch h hv hInputNonzero
  exact Full.tail h hw

end Sha1.Proofs.Buffered.Update.Slices
