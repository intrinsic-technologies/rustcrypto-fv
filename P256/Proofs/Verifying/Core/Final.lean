import P256.Proofs.Verifying.Core.Normalize.Coordinates
import P256.Proofs.Verifying.Core.Finish.Correct
import P256.Proofs.Verifying.Core.Output.Correct
import P256.Proofs.Verifying.Core.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Final

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar

theorem correct : Core.FinalCorrect := by
  intro _ s t boundary point result digest r scalarS pre state rip pointAt scalar output sum
    rPositive rBound sPositive sBound
  have scalar' : Nat256At t (stackPtr s-472) r := by
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using scalar
  obtain ⟨n,a,runA,stateA,outputA⟩ := Normalize.normalize pre state rip pointAt scalar'
  have outputA' : memLoad a.external (frameBase s+384) 64 = s.regValue .rdi := by
    have addr : frameBase s+384 = stackPtr s-792#64 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr] at output ⊢
    exact outputA.trans output
  obtain ⟨m,b,runB,stateB,ripB,outputB,tagB⟩ := Finish.finish
    (nonzero := decide (result.z ≠ 0)) pre stateA.toFrameState stateA.rip
    stateA.x stateA.y stateA.r15 (by
      by_cases zero : result.z=0
      · simpa [zero] using stateA.rbp
      · simpa [zero] using stateA.rbp)
    stateA.scalar outputA'
  have tag : (b.regValue .rax).setWidth 8 =
      if Ecdsa.verifies point.toAffine digest (r,scalarS) then 1 else 0 := by
    rw [selected_x,result_acceptance rPositive rBound sPositive sBound sum] at tagB
    exact tagB
  obtain ⟨k,u,runU,stateU,ripU,value⟩ := Output.correct pre stateB ripB outputB tag
  exact ⟨n+m+k,u,(runA.trans runB).trans runU,stateU,ripU,value⟩

end P256.Proofs.Verifying.Core.Final
