import P256.Proofs.Sec1Serialize.Tail.Initialize.Choice
import P256.Proofs.Sec1Serialize.Tail.Initialize.Zero.First
import P256.Proofs.Sec1Serialize.Tail.Initialize.Zero.Second

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem finish_preparation [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {infinity : Bool}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (entry : EncodedEntry s t boundary bytes infinity) :
    ∃ u, SelectionEntry s u boundary bytes infinity := by
  obtain ⟨u, prepared, rip⟩ := prepare_zero_first pre entry
  obtain ⟨v, chosen, rip, value⟩ := prepare_choose pre prepared rip
  exact prepare_zero_second_index pre chosen rip value

end P256.Proofs.Sec1Serialize
