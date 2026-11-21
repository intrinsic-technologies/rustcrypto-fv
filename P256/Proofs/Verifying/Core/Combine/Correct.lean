import P256.Proofs.Verifying.Core.Combine.Pack
import P256.Proofs.Verifying.Core.Combine.Call

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Combine

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

theorem combine [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {u v r : Nat} (pre : Core.Pre s boundary)
    (state : Input s t point u v r) (valid : point.valid)
    (combination : Combination.Correct) :
    ∃ fuel z result, Advances boundary fuel t z ∧ Frame s z ∧ z.RIP = 0x10de41 ∧
      ProjectiveAt z (frameBase s) result ∧ result.valid ∧
      result.toAffine = Points.add (Points.mul u Operations.domain.G) (Points.mul v point.toAffine) ∧
      Nat256At z (frameBase s+704#64) r ∧ memLoad z.external (frameBase s+384) 64 = s.regValue .rdi := by
  obtain ⟨n,a,runA,stateA⟩ := prepare_prefix pre state
  obtain ⟨m,b,runB,stateB⟩ := pack pre stateA
  obtain ⟨k,z,result,runZ,stateZ,ripZ,value,validZ,pointZ,savedR,output,_⟩ :=
    call pre stateB valid combination
  exact ⟨n+m+k,z,result,(runA.trans runB).trans runZ,stateZ,ripZ,value,validZ,pointZ,savedR,output⟩

end P256.Proofs.Verifying.Core.Combine
