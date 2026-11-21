import P256.Proofs.Signing.Core.Iteration.Digest
import P256.Proofs.Signing.Core.Iteration.Stages

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program SecretKeyFromBytes.Scalar

theorem correct_of_contracts (point : Point.Contract) (components : ComponentsContract)
    (output : OutputContract) : IterationContract := by
  intro bindings s t boundary state secret nonce digest pre input candidate rip execution
  obtain ⟨n,a,runA,ripA,stateA⟩ := Candidate.correct pre candidate rip
  obtain ⟨m,b,runB,ripB,stateB,digestB,inverseB,rbxB⟩ := Digest.correct pre input stateA ripA
  have pointInput : Point.Input s b nonce :=
    ⟨stateB.frame,stateB.scalar,stateB.positive,stateB.canonical,stateB.rbp,stateB.r13,rbxB,stateB.r15⟩
  obtain ⟨k,c,x,y,runC,ripC,affineC,encodedC,preservedC⟩ := point pre pointInput ripB
  have bytes (offset len : Nat) (live : ∀ i < len, Point.LiveOffset (offset+i)) :
      ∀ i < len, c.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        b.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    intro i hi
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact preservedC _ (live i hi)
  have arguments := NextNonce.arguments_copy stateB.arguments
    (fun i live => preservedC i (by unfold Point.LiveOffset; omega))
  have generator := stateB.generator.copy
    (bytes 2160 72 (by intro i hi; unfold Point.LiveOffset; omega))
    ⟨stateB.generator.2.1.1,fun i hi =>
      (bytes 272 32 (by intro j hj; unfold Point.LiveOffset; omega) i hi).trans (stateB.generator.2.1.2 i hi)⟩
  have componentsInput : ComponentsInput s c state nonce x y digest :=
    ⟨encodedC,arguments,generator,
      ⟨inverseB.1,fun i hi =>
        (bytes 336 32 (by intro j hj; unfold Point.LiveOffset; omega) i hi).trans (inverseB.2 i hi)⟩,
      ⟨digestB.1,fun i hi =>
        (bytes 1296 32 (by intro j hj; unfold Point.LiveOffset; omega) i hi).trans (digestB.2 i hi)⟩,
      stateB.positive,stateB.canonical,affineC⟩
  obtain ⟨j,d,runD,ripD,stateD⟩ := components pre input componentsInput ripC
  obtain ⟨initialFuel,initialRun⟩ := execution
  have executionD := (((initialRun.trans runA).trans runB).trans runC).trans runD
  obtain ⟨h,u,runU,result⟩ := output pre stateD ripD ⟨initialFuel+n+m+k+j,executionD⟩
  exact ⟨n+m+k+j+h,u,(((runA.trans runB).trans runC).trans runD).trans runU,result⟩

end P256.Proofs.Signing.Core.Iteration
