import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Second

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Curve

theorem storeMagnitudes {a b : Registers} {m n : Ram} {sp src tables digits : BitVec 64}
    {k : Nat} (entry : RoutineEntry a m sp 0x558) (bound : k < domain.n)
    (state : Signs a m sp src tables digits k b n) :
    ∃ c o, Reaches .l10f3c5 b n .l10f4af c o ∧ SplitState a m sp src tables digits k c o := by
  obtain ⟨c, o, left, saved⟩ := storeFirstMagnitude entry bound state
  obtain ⟨d, q, right, result⟩ := storeSecondMagnitude entry saved
  exact ⟨d, q, left.trans right, result⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
