import P256.Proofs.Verifying.Message.Hash.Finalize.Copy.Correct
import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Correct
import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Buffered initial s boundary message) :
    ∃ t, Result initial t boundary message := by
  obtain ⟨a, copied⟩ := copy pre state
  obtain ⟨b, padded⟩ := pad pre copied
  exact compress pre padded

end P256.Proofs.Verifying.Message.Hash.Finalize
