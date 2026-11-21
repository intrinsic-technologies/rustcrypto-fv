import P256.Proofs.Verifying.Core.Scalars.Correct
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.CoreCall
import P256.Proofs.Verifying.Core.Combine.Correct
import P256.Proofs.Verifying.Core.Final

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar

set_option maxHeartbeats 800000 in
theorem correct_of_combination (combination : Combination.Correct) : Core.Correct := by
  intro inst s entry boundary point digest r scalarS pre frame rip input valid rPositive rBound sPositive sBound
  obtain ⟨n,a,runA,stateA⟩ := Scalars.prepare_of_inverse Inverse.SafeGcd.core_stage
    pre frame rip input rPositive sPositive sBound
  have combineInput : Combine.Input s a point
      (Standards.SECG.ECC.ECDSA.digestToInt Operations.domain.n digest *
        Standards.SECG.ECC.Curve.inverse Operations.domain.n scalarS % Operations.domain.n)
      (r * Standards.SECG.ECC.Curve.inverse Operations.domain.n scalarS % Operations.domain.n) r :=
    ⟨stateA.toFrameState,stateA.rip,stateA.key,stateA.output,
      stateA.first,stateA.second,stateA.savedR⟩
  obtain ⟨m,b,result,runB,stateB,ripB,pointB,_,sum,rB,outputB⟩ :=
    Combine.combine pre combineInput valid combination
  have sum' : result.toAffine = Verifying.verificationPoint point.toAffine digest r scalarS := sum
  obtain ⟨k,u,runU,frameU,ripU,value⟩ := Final.correct pre stateB ripB pointB rB outputB sum'
    rPositive rBound sPositive sBound
  exact ⟨n+m+k,u,(runA.trans runB).trans runU,frameU,ripU,value⟩

end P256.Proofs.Verifying.Core
