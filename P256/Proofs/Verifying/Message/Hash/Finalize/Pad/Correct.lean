import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Load
import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Mark
import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Fill.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem pad [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Copied initial s boundary message) :
    ∃ t, Padded initial t boundary message := by
  obtain ⟨loaded, loadResult⟩ := Pad.load pre state
  obtain ⟨marked, markResult⟩ := Pad.mark pre loadResult
  exact Pad.fill pre markResult

end P256.Proofs.Verifying.Message.Hash.Finalize
