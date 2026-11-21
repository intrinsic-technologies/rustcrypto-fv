import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Load
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Mark
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Fill.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem pad [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (state : Copied initial start s message) :
    ∃ t, Padded initial start t message := by
  obtain ⟨loaded, loadResult⟩ := Pad.load pre state
  obtain ⟨marked, markResult⟩ := Pad.mark pre loadResult
  exact Pad.fill pre markResult

end P256.Proofs.Signing.Wrapper.Hash.Finalize
