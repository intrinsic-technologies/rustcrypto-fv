import K256.Proofs.Signing.Composition.Attempt.Return.Constructor
import K256.Proofs.Signing.Composition.Attempt.Return.Retry
import K256.Proofs.Signing.Composition.Attempt.Return.Recovery
import K256.Proofs.Signing.Composition.Attempt.Return.Epilogue

namespace K256.Proofs.Signing.Composition.Attempt

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)

theorem finish {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {r sigS : Nat}
    (words : SignatureScalars s d msg st r sigS a m) (rBound : r < domain.n) (sBound : sigS < domain.n) :
    if r = 0 ∨ sigS = 0 then
      ∃ b n, Reach (core .l105ce7 a m) (core .l105886 b n) ∧ Outer s d msg st b n
    else
      ∃ b n, Reach (core .l105ce7 a m) ⟨⟨.l102795,b,n⟩,[]⟩ ∧ Result s (r,sigS) b n := by
  obtain ⟨b,n,p,constructed⟩ := Return.construct call words rBound sBound
  split
  next zero =>
    obtain ⟨c,t,q,next⟩ := Return.retry call constructed zero
    exact ⟨c,t,p.trans q,next⟩
  next nz =>
    obtain ⟨c,t,q,normalized⟩ := Return.success call constructed nz rBound sBound
    obtain ⟨e,u,v,result⟩ := Return.epilogue call normalized
    exact ⟨e,u,(p.trans q).trans v,result⟩

end K256.Proofs.Signing.Composition.Attempt
