import K256.Proofs.Signing.Nonce.Initialize.Seed.Reduce.Arithmetic
import K256.Proofs.Signing.Nonce.Initialize.Seed.Reduce.Prepare
import K256.Proofs.Signing.Nonce.Initialize.Seed.Reduce.Select

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

theorem reduceDigest {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {x : Nat}
    (depth : 2208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 2208)
    (limit : fr.rsp.toNat + 784 < 2^32)
    (bound : x < 2^256) (ready : DigestLimbs fr a m x) :
    ∃ b n, Verify.Core.Reaches .l1010ae a m .l10126c b n ∧
      ReducedLimbs fr b n (x % Secp256k1.domain.n) := by
  obtain ⟨b,n,call,entry⟩ := prepareDigestSelect depth low limit bound ready
  obtain ⟨out,run,tag,result⟩ := selectDigest depth low limit (digestChoice bound).1 entry
  exact ⟨out.values,out.store,Verify.reachesOfCall call run tag,result⟩

end K256.Proofs.Signing.Nonce.Initialize
