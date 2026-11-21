import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.Fill
import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.Shift

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

theorem parseDigest {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {digest : ByteArray}
    (depth : 2208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 2208)
    (limit : fr.rsp.toNat + 784 < 2^32)
    (window : Writable Extracted.programImage fr.original fr.rsp 784)
    (digestPtr : fr.rcx = fr.rsp + 376) (digestLen : fr.r8 = 32)
    (hash : (⟨fr.rcx.toNat, 32⟩ : MemoryRegion).HasBytes fr.original digest)
    (ready : DigestLength fr a m) :
    ∃ b n, Verify.Core.Reaches .l101026 a m .l1010ae b n ∧
      DigestLimbs fr b n (Encoding.octetsToNat digest) := by
  obtain ⟨c, o, fill, filled⟩ := fillSeedDigest depth low limit window digestPtr digestLen hash ready
  obtain ⟨b, n, shift, limbs⟩ := shiftSeedDigest depth low limit filled
  exact ⟨b, n, fill.trans shift, limbs⟩

end K256.Proofs.Signing.Nonce.Initialize
