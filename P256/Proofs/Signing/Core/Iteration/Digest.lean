import P256.Proofs.Signing.Core.Iteration.Digest.Read
import P256.Proofs.Signing.Core.Iteration.Digest.Reduce
import P256.Proofs.Signing.Core.Iteration.Digest.Invert.Call
import P256.Proofs.Signing.Core.Iteration.Digest.Invert.Finish

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program SecretKeyFromBytes.Scalar Standards.SECG.ECC

theorem correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {nonce secret : Nat} {digest : ByteArray}
    (pre : SignPre s boundary) (input : SignInput s secret digest)
    (validated : Candidate.Validated s t state nonce) (rip : t.RIP = 0x10cbed) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cd5b ∧
      NonceState s u state nonce ∧
      Nat256At u (frameBase s+1296) (Arith.uint digest % Operations.domain.n) ∧
      Nat256At u (frameBase s+336) (Curve.inverse Operations.domain.n nonce) ∧ u.regValue .rbx = frameBase s+304 := by
  obtain ⟨n,a,runA,ripA,stateA⟩ := setup pre validated rip
  obtain ⟨m,b,runB,ripB,stateB,valueB⟩ := read pre input stateA ripA
  obtain ⟨k,c,runC,ripC,stateC,valueC⟩ := reduce pre stateB valueB ripB
  obtain ⟨j,d,runD,ripD,stateD,valueD,inverseD,flagD,bxD⟩ := Invert.call pre stateC valueC ripC
  obtain ⟨h,u,runU,ripU,stateU,valueU,inverseU,bxU⟩ := Invert.finish pre stateD valueD inverseD bxD flagD ripD
  exact ⟨n+m+k+j+h,u,(((runA.trans runB).trans runC).trans runD).trans runU,ripU,stateU,valueU,inverseU,bxU⟩

end P256.Proofs.Signing.Core.Iteration.Digest
