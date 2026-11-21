import K256.Proofs.Verify.Core.Scalars.Inverse.Adapter
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch
import K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}

theorem invertScalar (e : Entry fr a p digest r s) {b m} (h : Reduced fr b m digest r s) :
    ∃ c n, Reaches .l10518b b m .l1051b1 c n ∧ Inverted fr c n digest r s := by
  exact Scalars.Inverse.Adapter.execute
    (Scalars.Inverse.Batch.execute @Scalars.Inverse.modularShift) e h

end K256.Proofs.Verify.Core
