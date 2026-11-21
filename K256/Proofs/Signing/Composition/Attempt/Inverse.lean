import K256.Proofs.Signing.Composition.Attempt.Inverse.Core
import K256.Proofs.Signing.Composition.Attempt.Inverse.Wrapper
import K256.Proofs.Signing.Composition.Attempt.Inverse.Digest

namespace K256.Proofs.Signing.Composition.Attempt

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)

theorem invertAndReduceDigest {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {k : Nat}
    (parsed : NonceParsed s d msg st k a m) (pos : 0 < k) (bound : k < domain.n) :
    ∃ b n, Reach (core .l1059fb a m) (core .l105b23 b n) ∧ ScalarsReady s d msg st k b n := by
  obtain ⟨b,n,first,reduced⟩ := Inverse.reduceDigest call parsed
  obtain ⟨c,q,second,ready⟩ := Inverse.invertNonce Inverse.execute call reduced pos bound
  exact ⟨c,q,first.trans second,ready⟩

end K256.Proofs.Signing.Composition.Attempt
