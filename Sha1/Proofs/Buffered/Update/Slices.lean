import Sha1.Proofs.Buffered.Update.Slices.Branch
import Sha1.Proofs.Buffered.Update.Slices.Short
import Sha1.Proofs.Buffered.Update.Slices.Full

namespace Sha1.Proofs.Buffered.Update

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem update_family [bindings : Bindings]
    {boundary : ReturnBoundary} {message input : ByteArray} {s : RamState}
    (h : UpdatePre .updateFinalize boundary message input s)
    (hInputNonzero : (UpdateKind.inputRegion .updateFinalize s input).start ≠ 0) :
    ∃ t, UpdatePost .updateFinalize boundary message input s t := by
  obtain ⟨u, b⟩ := Slices.branch h
  by_cases hs : input.size < 64 - message.size % 64
  · exact Slices.short h b hs
  · exact Slices.full h b (by omega) hInputNonzero

end Sha1.Proofs.Buffered.Update
