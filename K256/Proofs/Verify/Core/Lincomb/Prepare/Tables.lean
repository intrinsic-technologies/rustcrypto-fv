import K256.Proofs.Verify.Core.Lincomb.Prepare.SecondTable

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

theorem tables {a b : Registers} {m n : Ram} {sp tables digits : BitVec 64}
    {p : Curve.Point} {k : Nat} (entry : RoutineEntry a m sp 0x558)
    (tableWrite : Writable Extracted.programImage m tables 1920)
    (digitsWrite : Writable Extracted.programImage m digits 544)
    (tableApart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩, ⟨digits.toNat, 544⟩] tables 1920)
    (digitsApart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    (bases : Bases a m sp tables digits p k b n) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10f82a, b, n⟩, []⟩ out ∧
      RoutineReturn a m sp 0x558 [⟨tables.toNat, 1920⟩, ⟨digits.toNat, 544⟩] out ∧
      Prepared out.store tables digits p k := by
  let layout : TableLayout a m sp tables digits := ⟨entry,tableWrite,digitsWrite,tableApart,digitsApart⟩
  obtain ⟨c,o,path,start⟩ := firstTable layout bases
  obtain ⟨out,run,ret,prepared⟩ := finishTables layout bases start
  exact ⟨out,Program.Exec.of_sem (path.exec run.sem),ret,prepared⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
