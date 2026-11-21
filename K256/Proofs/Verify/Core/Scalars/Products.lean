import K256.Proofs.Verify.Core.Scalars.Products.Digest
import K256.Proofs.Verify.Core.Scalars.Products.Signature

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}

theorem multiplyScalars (e : Entry fr a p digest r s) {b m} (h : Inverted fr b m digest r s) :
    ∃ c n, Reaches .l1051b1 b m .l105256 c n ∧
      Products fr c n (digestScalar digest s) (signatureScalar r s) r := by
  obtain ⟨c, n, first, prod⟩ := multiplyDigest e h
  obtain ⟨d, o, second, both⟩ := multiplySignature e prod
  exact ⟨d, o, first.trans second, both⟩

end K256.Proofs.Verify.Core
