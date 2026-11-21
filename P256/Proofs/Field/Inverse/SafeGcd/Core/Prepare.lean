import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Routine
import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.BatchStage

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem run_batch [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111f1a)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hpos : 1 ≤ s.remaining) (hbound : s.remaining ≤ 591)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1179fa initial).arguments
      initial.external (loopAtoms fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x111cd1 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l1177b1 final).arguments final.external
        (afterBatchAtoms fr controls p s) := by
  obtain ⟨n1, s1, e1, ready1, rip1, frame1, atoms1⟩ :=
    advances hcode hready hrip hframe hout hpos hbound hcore
  obtain ⟨n2, s2, e2, ready2, rip2, frame2, atoms2⟩ :=
    batch_advances hcode ready1 rip1 frame1 hout hpos atoms1
  exact ⟨n1+n2, s2, e1.trans e2, ready2, rip2, frame2, atoms2⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare
