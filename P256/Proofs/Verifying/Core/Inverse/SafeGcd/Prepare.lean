import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.Routine
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.BatchStage

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem run_batch [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x1124fe)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code) (hzero : zeroWords s.g.words = false)
    (hpos : 1 ≤ s.remaining) (hbound : s.remaining ≤ 591)
    (hcore : Atom.All code (Machine.lifted.locationOf .l11454e initial).arguments
      initial.external (loopAtoms fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x1122c1 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l114311 final).arguments final.external
        (afterBatchAtoms fr controls p s) := by
  obtain ⟨n1, s1, e1, ready1, rip1, frame1, atoms1⟩ :=
    zero_advances false hcode hready hrip hframe hout hzero hcore
  have ha : Atom.All code (Machine.lifted.locationOf .l114574 s1).arguments s1.external
      (loopAtoms fr controls p s ++ [.gpr 2 s.g.words[0]]) := by
    change Atom.All code _ _ (loopAtoms fr controls p s ++ [.fact _, .gpr 2 s.g.words[0]]) at atoms1
    rw [Atom.all_append] at atoms1 ⊢
    exact ⟨atoms1.1, atoms1.2.2⟩
  obtain ⟨n2, s2, e2, ready2, rip2, frame2, atoms2⟩ :=
    advances hcode ready1 rip1 frame1 hout hpos hbound ha
  obtain ⟨n3, s3, e3, ready3, rip3, frame3, atoms3⟩ :=
    batch_advances hcode ready2 rip2 frame2 hout hpos atoms2
  exact ⟨n1+n2+n3, s3, (e1.trans e2).trans e3, ready3, rip3, frame3, atoms3⟩

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare
