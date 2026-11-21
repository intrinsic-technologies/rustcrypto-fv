import P256.Proofs.Projective.Add.Call
import P256.Proofs.Projective.Add.Products
import P256.Proofs.Projective.Add.CrossTerms
import P256.Proofs.Projective.Add.Combinations
import P256.Proofs.Projective.Add.Output
import P256.Proofs.Projective.Add.Frame.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Projective

open P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem projective_add_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {left right : Projective} (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (leftAt : ProjectiveAt s (s.regValue .rdi) left)
    (rightAt : ProjectiveAt s (s.regValue .rsi) right) :
    ∃ t, CalleeResult s t boundary 96 920 ∧
      ProjectiveAt t (s.regValue .rdi) (left.add right) := by
  obtain ⟨_, a, runA, stateA, ripA, valueA⟩ := Add.products_correct pre leftAt rightAt
  obtain ⟨_, b, runB, stateB, ripB, valueB⟩ := Add.cross_terms_correct pre stateA ripA valueA
  obtain ⟨_, c, runC, stateC, ripC, valueC⟩ := Add.combinations_correct pre stateB ripB valueB
  obtain ⟨_, d, runD, stateD, ripD, valueD⟩ := Add.output_correct pre stateC ripC valueC
  obtain ⟨t, result, memory⟩ := Add.epilogue pre stateD ripD
    ⟨_, ((runA.trans runB).trans runC).trans runD⟩
  exact ⟨t, result, valueD.of_bytes_eq (fun i _ => by rw [memory])⟩

end P256.Proofs.Projective
