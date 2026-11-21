import P256.Proofs.Sec1Serialize.Tail.Finish.CopyResult
import P256.Proofs.Sec1Serialize.Tail.Finish.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem finish_serialization [Bindings] {s t : RamState}
    {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (entry : SelectionExit s t boundary bytes) :
    ∃ u, CalleeResult s u boundary 65 328 ∧ u.regValue .rax = s.regValue .rdi ∧
      (registerRegion s .rdi 65).HasBytes u.external bytes := by
  obtain ⟨v, setup⟩ := copy_setup pre entry
  obtain ⟨w, state, execution, rip, destination, output⟩ := copy_result pre setup
  obtain ⟨u, result, rax, memory⟩ :=
    serialization_epilogue pre state execution rip destination
  exact ⟨u, result, rax, memory ▸ output⟩

end P256.Proofs.Sec1Serialize
