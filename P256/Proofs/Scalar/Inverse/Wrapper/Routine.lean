import P256.Proofs.Scalar.Inverse.Wrapper.Return
import P256.Proofs.Scalar.Inverse.Wrapper.Prefix
import P256.Proofs.Scalar.Inverse.Wrapper.CoreCall
import P256.Proofs.Scalar.Inverse.Wrapper.ChoiceCall

namespace P256.Proofs.Scalar.Inverse.Wrapper

open P256.Proofs.Field.Inverse.SafeGcd
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112e30)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code) (hoff : fr.ret ≠ boundary.rip ∨ fr.rsp + 8 ≠ boundary.rsp)
    (hcore : Atom.All code (Machine.lifted.locationOf .l118910 initial).arguments
      initial.external (entryAtoms fr p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      Machine.Inverse.Post fr [outputRegion fr] final ∧
      WordsAt final.external fr.rdi 64 (resultWords p) ∧
      memLoad final.external (fr.rdi + 32) 8 = resultChoice p ∧
      Readable final.external fr.rdi 33 ∧ final.regValue .rax = fr.rdi ∧ final.MXCSR = p.mxcsr ∧ final.FP87_Control = p.fcw := by
  obtain ⟨n1, s1, e1, ready1, rip1, frame1, atoms1⟩ :=
    core_prefix hcode hready hrip hframe hout hcore
  obtain ⟨n2, s2, e2, ready2, rip2, frame2, atoms2⟩ :=
    core_stage hcode ready1 rip1 frame1 hout atoms1
  obtain ⟨n3, s3, e3, ready3, rip3, frame3, atoms3⟩ :=
    choice_prefix hcode ready2 rip2 frame2 hout atoms2
  obtain ⟨n4, s4, e4, ready4, rip4, frame4, atoms4⟩ :=
    choice_stage hcode ready3 rip3 frame3 hout atoms3
  obtain ⟨n5, s5, e5, ready5, post, hw, hc, hr, hx, hmx, hfc⟩ :=
    finish_stage hcode ready4 rip4 frame4 hout hoff atoms4
  exact ⟨n1+n2+n3+n4+n5, s5, (((e1.trans e2).trans e3).trans e4).trans e5,
    ready5, post, hw, hc, hr, hx, hmx, hfc⟩

end P256.Proofs.Scalar.Inverse.Wrapper
