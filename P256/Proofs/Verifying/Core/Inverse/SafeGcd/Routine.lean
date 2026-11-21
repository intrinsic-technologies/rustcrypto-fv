import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Loop
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Tail.Return
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Tail.Prefix
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Tail.Call

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112190)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code) (hoff : fr.ret ≠ boundary.rip ∨ fr.rsp + 8 ≠ boundary.rsp)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1141e0 initial).arguments
      initial.external (Prefix.atoms .entry fr controls p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      Machine.Core.Post fr [outputRegion fr] final ∧
      WordsAt final.external fr.rdi 64 (resultWords p) ∧
      memLoad final.external (fr.rdi + 32) 8 = resultChoice p ∧
      Readable final.external fr.rdi 33 ∧ final.MXCSR = controls.MXCSR ∧ final.FP87_Control = controls.FP87_Control := by
  obtain ⟨n1, s1, e1, ready1, rip1, frame1, atoms1⟩ :=
    Loop.initialized hcode hready hrip hframe hout hcore
  obtain ⟨n2, s2, e2, ready2, rip2, frame2, atoms2⟩ :=
    Tail.Prefix.advances hcode ready1 rip1 frame1 hout atoms1
  obtain ⟨n3, s3, e3, ready3, rip3, frame3, atoms3⟩ :=
    Tail.correction_call hcode ready2 rip2 frame2 hout atoms2
  obtain ⟨n4, s4, e4, ready4, post, hw, hc, hr, mx, fc⟩ :=
    Tail.finish_stage hcode ready3 rip3 frame3 hout hoff atoms3
  exact ⟨n1+n2+n3+n4, s4, ((e1.trans e2).trans e3).trans e4,
    ready4, post, hw, hc, hr, mx, fc⟩

end P256.Proofs.Verifying.Core.Inverse.SafeGcd
