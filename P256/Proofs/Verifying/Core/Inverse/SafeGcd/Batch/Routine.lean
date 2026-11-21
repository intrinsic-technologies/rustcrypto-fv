import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch.Step
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Batch.Arithmetic

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Words} {count : Nat}
    {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112625)
    (hframe : RamWriteFrame fr.original initial.external [])
    (hout : ReturnOutside boundary code) (hpos : 1 ≤ count) (hbound : count ≤ 62)
    (hcore : Atom.All code (Machine.lifted.locationOf .l114675 initial).arguments
      initial.external (loopAtoms fr controls p count)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x1122c1 ∧ RamWriteFrame fr.original final.external [] ∧
      Atom.All code (Machine.lifted.locationOf .l114311 final).arguments final.external
        (finishAtoms true fr controls (run count p) 0) := by
  induction count generalizing initial p with
  | zero => omega
  | succ count ih =>
    cases count with
    | zero =>
      exact step true hcode hready hrip hframe hout hpos hbound rfl hcore
    | succ count =>
      obtain ⟨n1,s1,e1,ready1,rip1,frame1,atoms1⟩ :=
        step false hcode hready hrip hframe hout hpos hbound (by simp) hcore
      have ha : Atom.All code (Machine.lifted.locationOf .l114675 s1).arguments s1.external
          (loopAtoms fr controls (next p) (count+1)) := by
        simpa only [finishAtoms, exitLabel, Nat.add_sub_cancel] using atoms1
      obtain ⟨n2,s2,e2,ready2,rip2,frame2,atoms2⟩ :=
        ih ready1 rip1 frame1 (by omega) (by omega) ha
      exact ⟨n1+n2,s2,e1.trans e2,ready2,rip2,frame2,atoms2⟩

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch
