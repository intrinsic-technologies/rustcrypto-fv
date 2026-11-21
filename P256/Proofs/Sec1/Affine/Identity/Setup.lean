import P256.Proofs.Sec1.Affine.Dispatch.Entry
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Identity

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : AffineDecodePre s boundary ⟨#[0]⟩)
    (state : Tagged s t 0) (rip : t.RIP = 0x110612) :
    ∃ u, Advances boundary 5 t u ∧ Frame s u ∧ u.RIP = 0x110629 ∧
      u.regValue .rbx = s.regValue .rdi ∧ u.regValue .rdi = s.regValue .rdi ∧
      u.regValue .rsi = 0x202df8 ∧ u.regValue .rcx = 9 := by
  obtain ⟨a, aa, ra, ea⟩ := (test_r32_r32_effect_step 0x110612 0xc9 rfl).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10612 _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10614 (by decide)))
  have ga : AgreesExcept [.flags, .rip] t a := ea.agrees
  have sa := state.toFrameState.after_registers ra ga (by simp [Component.Covers]) (by simp)
  have cx : t.regValue .rcx = 0 := state.tagCopy
  have condition : condHolds 5 (StatusFlags.ofRFLAGS a.RFLAGS) = false := by
    have h := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF =
      (((t.regValue .rcx).setWidth 32 &&& (t.regValue .rcx).setWidth 32) == 0) at h
    change (!(StatusFlags.ofRFLAGS a.RFLAGS).ZF) = false
    rw [h, cx]
    decide +kernel
  obtain ⟨b, ab, rb, eb⟩ := (jcc_rel32_effect_step 0x110614 5 0x71d).advances ra
    (programText_slice (programLoaded_codeIn sa.loaded) 0x10614 _
      (by decide) (by decide +kernel)) ⟨ea.rip, fun _ => by decide⟩
    (by simpa only [jccEffect, condition, branchEffect, Bool.false_eq_true, ite_false,
        BitVec.reduceAdd, Extracted.textAddress] using
      boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1061a (by decide)))
  have gb : AgreesExcept [.rip] a b := eb.agrees
  have sb := sa.after_registers rb gb (by simp [Component.Covers]) (by simp)
  have ip : b.RIP = 0x11061a := eb.rip.trans (by
    simp only [jccEffect, condition, branchEffect, Bool.false_eq_true, ite_false]; rfl)
  obtain ⟨c, ac, rc, ec⟩ := (mov_r32_imm32_effect_step 0x11061a 0xb9 (by decide) 9).advances rb
    (programText_slice (programLoaded_codeIn sb.loaded) 0x1061a _
      (by decide) (by decide +kernel)) ip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1061f (by decide)))
  have gc : AgreesExcept [.reg 1, .rip] b c := ec.agrees
  have sc := sb.after_registers rc gc (by simp [Component.Covers]) (by simp)
  obtain ⟨d, ad, rd, ed⟩ := (mov_r64_r64_effect_step 0x11061f 0x48 0xdf
    (by simp [RexWPrefix]) rfl).advances rc
    (programText_slice (programLoaded_codeIn sc.loaded) 0x1061f _
      (by decide) (by decide +kernel)) ec.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10622 (by decide)))
  have gd : AgreesExcept [.reg 7, .rip] c d := ed.agrees
  have sd := sc.after_registers rd gd (by simp [Component.Covers]) (by simp)
  obtain ⟨u, au, ru, eu⟩ := (mov_r64_imm32_effect_step 0x110622 0x48 0xc6
    (by simp [RexWPrefix]) rfl rfl 0x202df8).advances rd
    (programText_slice (programLoaded_codeIn sd.loaded) 0x10622 _
      (by decide) (by decide +kernel)) ed.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10629 (by decide)))
  have gu : AgreesExcept [.reg 6, .rip] d u := eu.agrees
  have total := (((ga.trans gb).trans gc).trans gd).trans gu
  refine ⟨u, (((aa.trans ab).trans ac).trans ad).trans au,
    sd.after_registers ru gu (by simp [Component.Covers]) (by simp), eu.rip,
    (total.read (n := 64) (r := 3) (by simp)).trans state.output, ?_, eu.writes, ?_⟩
  · exact (gu.read (n := 64) (r := 7) (by simp)).trans (ed.writes.trans
      ((((ga.trans gb).trans gc).read (n := 64) (r := 3) (by simp)).trans state.output))
  · exact ((gd.trans gu).read (n := 64) (r := 1) (by simp)).trans ec.writes

end P256.Proofs.Sec1.Affine.Identity
