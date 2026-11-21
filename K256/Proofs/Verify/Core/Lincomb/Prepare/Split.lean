import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls
import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Compare
import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Magnitude

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

theorem splitScalar {a : Registers} {m : Ram} {sp src scalar tables digits : BitVec 64}
    {k : Nat} (entry : RoutineEntry a m sp 0x558)
    (di : a[7] = ⟨64, src⟩) (si : a[6] = ⟨64, scalar⟩) (dx : a[2] = ⟨64, tables⟩)
    (cx : a[1] = ⟨64, digits⟩) (bound : k < domain.n)
    (words : WordsAt m scalar 64 (Generate.Generator.Multiply.scalarWords k))
    (scalarRead : Readable m scalar 32)
    (scalarApart : Outside [scratch sp 0x558] scalar 32) :
    ∃ b n, Reaches .l10f150 a m .l10f4af b n ∧ SplitState a m sp src tables digits k b n := by
  obtain ⟨b, n, calls, residues⟩ := splitResidues entry di si dx cx bound words scalarRead scalarApart
  obtain ⟨c, o, compare, signs⟩ := compareResidues entry bound residues
  obtain ⟨d, q, store, result⟩ := storeMagnitudes entry bound signs
  exact ⟨d, q, calls.trans (compare.trans store), result⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
