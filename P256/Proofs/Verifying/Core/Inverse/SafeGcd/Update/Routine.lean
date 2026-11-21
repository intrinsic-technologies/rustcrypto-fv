import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.FirstPrefix
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.FirstCall
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.SecondPrefix
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.SecondCall
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.CopyFG
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.ThirdPrefix
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.ThirdCall
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.FourthPrefix
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.FourthCall
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.CopyDE

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x1122c1)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code) (hpos : 1 ≤ s.remaining) (hbound : s.remaining ≤ 591)
    (hcore : Atom.All code (Machine.lifted.locationOf .l114311 initial).arguments
      initial.external (Prepare.afterBatchAtoms fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x1124ee ∧ RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l11453e final).arguments final.external
        (CopyDE.updatedAtoms fr controls p s) := by
  have hstart : Atom.All code (Machine.lifted.locationOf .l114311 initial).arguments
      initial.external (FirstPrefix.atoms .entry fr controls p s) := by
    change Atom.All code _ _ (Prepare.afterBatchAtoms fr controls p s ++ bounds s)
    rw [Atom.all_append]
    exact ⟨hcore, hpos, hbound, trivial⟩
  obtain ⟨n1, s1, e1, ready1, rip1, frame1, atoms1⟩ :=
    FirstPrefix.advances hcode hready hrip hframe hout hstart
  obtain ⟨n2, s2, e2, ready2, rip2, frame2, atoms2⟩ :=
    first_call hcode ready1 rip1 frame1 hout atoms1
  obtain ⟨n3, s3, e3, ready3, rip3, frame3, atoms3⟩ :=
    SecondPrefix.advances hcode ready2 rip2 frame2 hout atoms2
  obtain ⟨n4, s4, e4, ready4, rip4, frame4, atoms4⟩ :=
    second_call hcode ready3 rip3 frame3 hout atoms3
  obtain ⟨n5, s5, e5, ready5, rip5, frame5, atoms5⟩ :=
    CopyFG.advances hcode ready4 rip4 frame4 hout atoms4
  obtain ⟨n6, s6, e6, ready6, rip6, frame6, atoms6⟩ :=
    ThirdPrefix.advances hcode ready5 rip5 frame5 hout atoms5
  obtain ⟨n7, s7, e7, ready7, rip7, frame7, atoms7⟩ :=
    third_call hcode ready6 rip6 frame6 hout atoms6
  obtain ⟨n8, s8, e8, ready8, rip8, frame8, atoms8⟩ :=
    FourthPrefix.advances hcode ready7 rip7 frame7 hout atoms7
  obtain ⟨n9, s9, e9, ready9, rip9, frame9, atoms9⟩ :=
    fourth_call hcode ready8 rip8 frame8 hout atoms8
  obtain ⟨n10, s10, e10, ready10, rip10, frame10, atoms10⟩ :=
    CopyDE.advances hcode ready9 rip9 frame9 hout atoms9
  exact ⟨n1+n2+n3+n4+n5+n6+n7+n8+n9+n10, s10, (((((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7).trans e8).trans e9).trans e10), ready10, rip10, frame10, atoms10⟩

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update
