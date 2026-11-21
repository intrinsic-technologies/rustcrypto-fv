import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.First
import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.Endomorphism
import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.Second
import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.Double

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

theorem signedBases {a b : Registers} {m n : Ram} {sp src tables digits : BitVec 64}
    {p : Projective} {k : Nat} (entry : RoutineEntry a m sp 0x558) (valid : p.valid)
    (point : p.Stored m src) (pointRead : Readable m src 120)
    (pointApart : Outside [scratch sp 0x558, ⟨digits.toNat, 544⟩] src 120)
    (digitsWrite : Writable Extracted.programImage m digits 544)
    (digitsApart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    (recoded : Recoded a m sp src tables digits k b n) :
    ∃ c o, Reaches .l10f52c b n .l10f82a c o ∧ Bases a m sp tables digits p.value k c o := by
  obtain ⟨c,o,firstPath,firstBase,source⟩ := firstSignedBase entry valid point pointRead pointApart digitsWrite digitsApart recoded
  obtain ⟨d,r,endoPath,firstBase',endo⟩ := applyEndomorphism entry valid point pointRead pointApart digitsWrite digitsApart firstBase source
  obtain ⟨f,t,secondPath,pair⟩ := secondSignedBase entry digitsWrite digitsApart firstBase' endo
  obtain ⟨g,u,doublePath,bases⟩ := doubleFirstBase entry digitsWrite digitsApart pair
  exact ⟨g,u,((firstPath.trans endoPath).trans secondPath).trans doublePath,bases⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
