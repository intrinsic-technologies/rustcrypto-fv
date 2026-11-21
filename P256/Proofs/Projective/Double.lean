import P256.Proofs.Projective.Double.Entry
import P256.Proofs.Projective.Double.Body
import P256.Proofs.Projective.Double.Store
import P256.Proofs.Projective.Double.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Projective

open P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem projective_double_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {inputRegister : Syntax.Reg} {point : Projective}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (input : ProjectiveAt s (s.regValue .rdi) point) :
    ∃ t, CalleeResult s t boundary 96 1016 ∧
      ProjectiveAt t (s.regValue .rdi) point.double := by
  obtain ⟨_, a, runA, stateA, ripA, valueA⟩ := Double.entry_correct pre input
  obtain ⟨_, b, runB, stateB, ripB, valueB⟩ := Double.body_correct pre stateA ripA valueA
  obtain ⟨c, runC, stateC, ripC, valueC⟩ := Double.copy_correct pre stateB ripB valueB
  obtain ⟨t, result, memory⟩ := Double.epilogue pre stateC ripC
    ⟨_, (runA.trans runB).trans runC⟩
  exact ⟨t, result, valueC.of_bytes_eq (fun i _ => by rw [memory])⟩

end P256.Proofs.Projective
