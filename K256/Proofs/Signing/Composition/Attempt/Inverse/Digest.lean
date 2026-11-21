import K256.Proofs.Signing.Composition.Attempt.Inverse.Digest.Fill
import K256.Proofs.Signing.Composition.Attempt.Inverse.Digest.Reduce
import K256.Proofs.Signing.Composition.Reach
import K256.Proofs.Signing.Transfer.Verify

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult)

theorem reduceDigest {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg]) {a : Registers} {m : Ram} {st : State} {k : Nat}
    (parsed : NonceParsed s d msg st k a m) :
    ∃ b n, Reach (core .l1059fb a m) (core .l105afc b n) ∧ DigestReduced s d msg st k b n := by
  obtain ⟨b,n,firstRun,filled⟩ := fillDigest call parsed
  obtain ⟨c,t,suffix,reduced⟩ := reduceFilledDigest call filled
  have trace := Transfer.verifyReachesAt (src := .l1059fb) (dst := .l1059fb)
    (src' := .l105afc) (dst' := .l105afc) rfl rfl (firstRun.trans suffix)
  exact ⟨c,t,appendStack trace [resume .l102795 0x102795],reduced⟩

end K256.Proofs.Signing.Composition.Attempt.Inverse
