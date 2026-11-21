import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.Stage
import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.Serialize
import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.Parity
import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.High
import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.Normalize

namespace K256.Proofs.Signing.Composition.Attempt.Return

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)

theorem success {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {r sigS : Nat}
    (input : Constructed s d msg st r sigS a m) (nz : ¬ (r = 0 ∨ sigS = 0))
    (rBound : r < domain.n) (sBound : sigS < domain.n) :
    ∃ b n, Reach (core .l105d35 a m) (core .l105e11 b n) ∧ Normalized s d r sigS b n := by
  obtain ⟨b,n,p,staged⟩ := Recovery.stage call input nz
  obtain ⟨c,t,q,serialized,bx⟩ := Recovery.serialize call staged
  obtain ⟨e,u,v,parity⟩ := Recovery.parity call serialized bx
  obtain ⟨f,w,h,high⟩ := Recovery.high call parity
  obtain ⟨g,x,k,normalized⟩ := Recovery.normalize call high nz rBound sBound
  exact ⟨g,x,(((p.trans q).trans v).trans h).trans k,normalized⟩

end K256.Proofs.Signing.Composition.Attempt.Return
