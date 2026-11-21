import K256.Proofs.Verify.Core.Lincomb.Prepare.Split
import K256.Proofs.Verify.Core.Lincomb.Prepare.Digits
import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases
import K256.Proofs.Verify.Core.Lincomb.Prepare.Tables

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

theorem prepare {a : Registers} {m : Ram} {sp src scalar tables digits : BitVec 64}
    {p : Projective} {k : Nat} (entry : RoutineEntry a m sp 0x558)
    (di : a[7] = ⟨64, src⟩) (si : a[6] = ⟨64, scalar⟩) (dx : a[2] = ⟨64, tables⟩)
    (cx : a[1] = ⟨64, digits⟩) (bound : k < domain.n) (valid : p.valid)
    (point : p.Stored m src) (words : WordsAt m scalar 64 (Generate.Generator.Multiply.scalarWords k))
    (pointRead : Readable m src 120) (scalarRead : Readable m scalar 32)
    (pointApart : Outside [scratch sp 0x558, ⟨tables.toNat, 1920⟩, ⟨digits.toNat, 544⟩] src 120)
    (scalarApart : Outside [scratch sp 0x558, ⟨tables.toNat, 1920⟩, ⟨digits.toNat, 544⟩] scalar 32)
    (tableWrite : Writable Extracted.programImage m tables 1920)
    (digitsWrite : Writable Extracted.programImage m digits 544)
    (tableApart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩, ⟨digits.toNat, 544⟩] tables 1920)
    (digitsApart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    (zero : DigitBytes m (digits + 8) [] ∧ DigitBytes m (digits + 0x118) []) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10f150, a, m⟩, []⟩ out ∧
      RoutineReturn a m sp 0x558 [⟨tables.toNat, 1920⟩, ⟨digits.toNat, 544⟩] out ∧
      Prepared out.store tables digits p.value k := by
  have sa : Outside [scratch sp 0x558] scalar 32 :=
    ⟨scalarApart.1, fun r hr => scalarApart.2 r (by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self)⟩
  have pa : Outside [scratch sp 0x558, ⟨digits.toNat, 544⟩] src 120 := by
    refine ⟨pointApart.1, fun r hr => pointApart.2 r ?_⟩
    simp only [List.mem_cons] at hr ⊢
    exact hr.imp_right Or.inr
  obtain ⟨b, n, path₁, split⟩ := Prepare.splitScalar entry di si dx cx bound words scalarRead sa
  obtain ⟨c, o, path₂, recoded⟩ := Prepare.encodeDigits entry bound digitsWrite digitsApart zero split
  obtain ⟨d, q, path₃, bases⟩ := Prepare.signedBases entry valid point pointRead pa digitsWrite digitsApart recoded
  obtain ⟨out, run, ret, result⟩ := Prepare.tables entry tableWrite digitsWrite tableApart digitsApart bases
  exact ⟨out, Program.Exec.of_sem (((path₁.trans path₂).trans path₃).exec run.sem), ret, result⟩

end K256.Proofs.Verify.Core.Lincomb
