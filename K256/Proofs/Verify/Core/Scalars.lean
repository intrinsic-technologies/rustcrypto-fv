import K256.Proofs.Verify.Core.Scalars.Digest
import K256.Proofs.Verify.Core.Scalars.Inverse
import K256.Proofs.Verify.Core.Scalars.Products

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}

theorem scalarPath (e : Entry fr a p digest r s) {b m} (h : Parsed fr b m r s) :
    ∃ c n, Reaches .l1050c1 b m .l105256 c n ∧
      Products fr c n (digestScalar digest s) (signatureScalar r s) r := by
  obtain ⟨c, n, hc, reduced⟩ := reduceDigest e h
  obtain ⟨d, o, hd, inverted⟩ := invertScalar e reduced
  obtain ⟨f, q, hf, products⟩ := multiplyScalars e inverted
  exact ⟨f, q, (hc.trans hd).trans hf, products⟩

end K256.Proofs.Verify.Core
