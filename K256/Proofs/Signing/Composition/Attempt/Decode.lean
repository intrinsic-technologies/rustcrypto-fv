import K256.Proofs.Signing.Composition.Attempt.Decode.Accept

namespace K256.Proofs.Signing.Composition.Attempt

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)

theorem decode {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {k : Nat}
    (outer : Outer s d msg st a m) (pos : 0 < k) (bound : k < domain.n)
    (nonce : (⟨(sp s+384).toNat,32⟩ : MemoryRegion).HasBytes m (Encoding.natToOctets 32 k)) :
    ∃ b n, Reach (core .l1058d0 a m) (core .l1059fb b n) ∧ NonceParsed s d msg st k b n := by
  obtain ⟨b,n,parseRun,parsed⟩ := Decode.parse call outer bound nonce
  obtain ⟨c,o,selectRun,selected⟩ := Decode.select call parsed
  obtain ⟨e,p,compareRun,checked,zero⟩ := Decode.compare call selected pos bound
  obtain ⟨f,q,choiceRun,chosen,one⟩ := Decode.invertChoice call checked zero
  obtain ⟨g,t,acceptRun,ready⟩ := Decode.accept call chosen one
  exact ⟨g,t,parseRun.trans (selectRun.trans (compareRun.trans (choiceRun.trans acceptRun))),ready⟩

end K256.Proofs.Signing.Composition.Attempt
