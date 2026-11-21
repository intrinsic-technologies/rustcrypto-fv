import K256.Proofs.Signing.Composition.Attempt.Return.Constructor.Entry
import K256.Proofs.Signing.Composition.Attempt.Return.Constructor.Serialize
import K256.Proofs.Signing.Composition.Attempt.Return.Constructor.Decode
import K256.Proofs.Signing.Composition.Attempt.Return.Constructor.Finish

namespace K256.Proofs.Signing.Composition.Attempt.Return

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)

theorem construct {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {r sigS : Nat}
    (words : SignatureScalars s d msg st r sigS a m) (rBound : r < domain.n) (sBound : sigS < domain.n) :
    ∃ b n, Reach (core .l105ce7 a m) (core .l105d35 b n) ∧ Constructed s d msg st r sigS b n := by
  obtain ⟨b,n,h₁,entry⟩ := Constructor.enter call words
  obtain ⟨c,o,h₂,active,encoded⟩ := Constructor.first call entry
  obtain ⟨e,p,h₃,active,parsed⟩ := Constructor.decode call active encoded rBound
  obtain ⟨f,q,h₄,active,encoded⟩ := Constructor.second call active parsed
  obtain ⟨g,t,h₅,active,parsed⟩ := Constructor.decode call active encoded sBound
  obtain ⟨j,u,h₆,result⟩ := Constructor.finish call active parsed rBound sBound
  exact ⟨j,u,h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆)))),result⟩

end K256.Proofs.Signing.Composition.Attempt.Return
