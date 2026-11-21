import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Prefix
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Call
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Return

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x1116c0)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hoff : fr.ret ≠ boundary.rip ∨ fr.rsp + 8 ≠ boundary.rsp)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1171a0 initial).arguments
      initial.external (entryAtoms fr controls p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      Machine.Modular.Post fr [outputRegion fr] final ∧
      WordsAt final.external fr.rdi 64 (resultWords p) ∧
      memLoad final.external (fr.rdi + 32) 8 = resultSign p ∧
      Readable final.external fr.rdi 33 ∧
      final.MXCSR = controls.MXCSR ∧ final.FP87_Control = controls.FP87_Control := by
  obtain ⟨n1, s1, e1, ready1, rip1, frame1, atoms1⟩ :=
    linear_prefix hcode hready hrip hframe hout hcore
  obtain ⟨n2, s2, e2, ready2, rip2, frame2, atoms2⟩ :=
    linear_stage hcode ready1 rip1 frame1 hout atoms1
  obtain ⟨n3, s3, e3, ready3, post, hw, hs, hr, mx, fc⟩ :=
    finish_stage hcode ready2 rip2 frame2 hout hoff atoms2
  exact ⟨n1+n2+n3, s3, (e1.trans e2).trans e3, ready3, post, hw, hs, hr, mx, fc⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift
