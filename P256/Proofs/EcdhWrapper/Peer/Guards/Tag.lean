import P256.Proofs.Sec1.Decode.Header.Tag
import X86Proofs.Instructions.Mov.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Shr.Generated.R8Cl.Triple
import X86Proofs.Instructions.Test.Generated.AccImm8.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Guards

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Sec1.Decode.Header
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

private theorem tag_bound (tag : BitVec 8) (valid : validTag tag = true) :
    (!((cmpSpec (tag.setWidth 64) 5).CF || (cmpSpec (tag.setWidth 64) 5).ZF)) = false := by
  simp only [validTag, Bool.or_eq_true, beq_iff_eq] at valid
  rcases valid with (((h | h) | h) | h) | h
  all_goals subst tag; decide +kernel

private theorem tag_bit (tag : BitVec 8) (valid : validTag tag = true) :
    decide (((0x3d#8 >>> shiftCount 8 tag) &&& 1) = 0) = false := by
  simp only [validTag, Bool.or_eq_true, beq_iff_eq] at valid
  rcases valid with (((h | h) | h) | h) | h
  all_goals subst tag; decide +kernel

theorem tag_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x1069db)
    (readable : MemReadable s (s.regValue .r12) 1)
    (valid : validTag (memLoad s.external (s.regValue .r12) 8) = true) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ t.RIP = 0x1069f6 ∧
      t.regValue .rcx = (memLoad s.external (s.regValue .r12) 8).setWidth 64 ∧
      AgreesExcept [.reg 0, .reg 1, .flags, .rip] s t := by
  have addZero : s.regValue .r12 + 0 = s.regValue .r12 := BitVec.add_zero _
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (movzx_r32_m8_rex_effect_step 0x1069db 0x41 (by simp [RexNoWPrefix])
      1 (.sib 12 none 0 .none) (by decide) rfl rfl).advances ready
      (programText_slice code 0x69db _ (by decide) (by decide +kernel))
      ⟨rip, by change MemReadable s (s.regValue .r12 + 0) 1; simpa only [addZero] using readable⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x69e0 (by decide)))
  have g1 : AgreesExcept [.reg 1, .rip] s s1 := e1.agrees
  have m1 := g1.external (by simp [Component.Covers])
  have cx1 : s1.regValue .rcx = (memLoad s.external (s.regValue .r12) 8).setWidth 64 := by
    have h : s1.regValue .rcx = (memLoad s.external (s.regValue .r12 + 0) 8).setWidth 64 := e1.writes
    simpa only [addZero] using h
  obtain ⟨s2, a2, r2, e2⟩ := (mov_r8_imm8_effect_step 0x1069e0 0xb0 (by decide) 0x3d).advances
    r1 (programText_slice (code.of_external_eq m1) 0x69e0 _ (by decide) (by decide +kernel)) e1.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x69e2 (by decide)))
  have g2 : AgreesExcept [.reg 0, .rip] s1 s2 := e2.agrees
  have total2 := g1.trans g2
  have m2 := total2.external (by simp [Component.Covers])
  have al2 : (Operand.reg 0 : Operand 8).read s2 = 0x3d := by
    have h := e2.writes
    change (Operand.reg 0 : Operand 64).read s2 = mergeGPR 8 _ _ at h
    change ((Operand.reg 0 : Operand 64).read s2).setWidth 8 = _
    rw [h, mergeGPR_low8]
  have cl2 : (Operand.reg 1 : Operand 8).read s2 = memLoad s.external (s.regValue .r12) 8 := by
    have h : s2.regValue .rcx = (memLoad s.external (s.regValue .r12) 8).setWidth 64 :=
      (g2.read (n := 64) (r := 1) (by simp)).trans cx1
    change (s2.regValue .rcx).setWidth 8 = _
    rw [h, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  obtain ⟨s3, a3, r3, e3⟩ :=
    (shr_r8_cl_effect_step 0x1069e2 0xe8 (by decide) (by decide) (by decide)).advances
      r2 (programText_slice (code.of_external_eq m2) 0x69e2 _ (by decide) (by decide +kernel)) e2.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x69e4 (by decide)))
  change (shrR8ClEffect 0x1069e2 2 0 s2).Holds s2 s3 at e3
  have g3 : AgreesExcept [.reg 0, .flags, .rip] s2 s3 := e3.agrees
  have total3 := total2.trans g3
  have m3 := total3.external (by simp [Component.Covers])
  have al3 : (Operand.reg 0 : Operand 8).read s3 =
      0x3d#8 >>> shiftCount 8 (memLoad s.external (s.regValue .r12) 8) := by
    have h := e3.writes
    change (Operand.reg 0 : Operand 64).read s3 = mergeGPR 8 _ _ at h
    change ((Operand.reg 0 : Operand 64).read s3).setWidth 8 = _
    rw [h, mergeGPR_low8, al2, cl2]
    rfl
  obtain ⟨s4, a4, r4, e4⟩ :=
    (cmp_r64_imm8_effect_step 0x1069e4 0x48 0xf9 5 (by simp [RexWPrefix]) rfl rfl).advances
      r3 (programText_slice (code.of_external_eq m3) 0x69e4 _ (by decide) (by decide +kernel)) e3.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x69e8 (by decide)))
  have g4 : AgreesExcept [.flags, .rip] s3 s4 := e4.agrees
  have total4 := total3.trans g4
  have m4 := total4.external (by simp [Component.Covers])
  have cx3 : s3.regValue .rcx = (memLoad s.external (s.regValue .r12) 8).setWidth 64 :=
    ((g2.trans g3).read (n := 64) (r := 1) (by simp)).trans cx1
  have notAbove : condHolds 7 (StatusFlags.ofRFLAGS s4.RFLAGS) = false := by
    have cf := e4.flags.1
    have zf := e4.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s4.RFLAGS).CF = (cmpSpec (s3.regValue .rcx) 5).CF at cf
    change (StatusFlags.ofRFLAGS s4.RFLAGS).ZF = (cmpSpec (s3.regValue .rcx) 5).ZF at zf
    simp only [condHolds, cf, zf, cx3]
    exact tag_bound _ valid
  have branch4 : jccEffect 0x1069e8 6 7 ((0x300 : BitVec 32).signExtend 64) s4 =
      ({rip := 0x1069ee} : Effect) := by
    simp only [jccEffect, notAbove, branchEffect]
    rfl
  obtain ⟨s5, a5, r5, e5⟩ := (jcc_rel32_effect_step 0x1069e8 7 0x300).advances
    r4 (programText_slice (code.of_external_eq m4) 0x69e8 _ (by decide) (by decide +kernel))
    ⟨e4.rip, by intro; decide⟩
    (by rw [branch4]; exact boundary_ne_program outside (inProgram_of_textOffset 0x69ee (by decide)))
  rw [branch4] at e5
  have g5 : AgreesExcept [.rip] s4 s5 := e5.agrees
  have total5 := total4.trans g5
  have m5 := total5.external (by simp [Component.Covers])
  obtain ⟨s6, a6, r6, e6⟩ := (test_al_imm8_effect_step 0x1069ee 1).advances
    r5 (programText_slice (code.of_external_eq m5) 0x69ee _ (by decide) (by decide +kernel)) e5.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x69f0 (by decide)))
  have g6 : AgreesExcept [.flags, .rip] s5 s6 := e6.agrees
  have total6 := total5.trans g6
  have m6 := total6.external (by simp [Component.Covers])
  have zf6 : (StatusFlags.ofRFLAGS s6.RFLAGS).ZF = false := by
    have h := e6.flag .ZF
    change (StatusFlags.ofRFLAGS s6.RFLAGS).ZF =
      decide ((((Operand.reg 0 : Operand 8).read s5) &&& 1) = 0) at h
    rw [((g4.trans g5).read (n := 8) (r := 0) (by simp)).trans al3] at h
    exact h.trans (tag_bit _ valid)
  have branch6 : jccEffect 0x1069f0 6 4 ((0x2f8 : BitVec 32).signExtend 64) s6 =
      ({rip := 0x1069f6} : Effect) := by
    simp only [jccEffect, condHolds, zf6, branchEffect]
    rfl
  obtain ⟨t, runT, rt, et⟩ := (jcc_rel32_effect_step 0x1069f0 4 0x2f8).advances
    r6 (programText_slice (code.of_external_eq m6) 0x69f0 _ (by decide) (by decide +kernel))
    ⟨e6.rip, by intro; decide⟩
    (by rw [branch6]; exact boundary_ne_program outside (inProgram_of_textOffset 0x69f6 (by decide)))
  rw [branch6] at et
  refine ⟨t, (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans runT,
    rt, et.rip, ?_, ?_⟩
  · exact (((((g2.trans g3).trans g4).trans g5).trans g6).trans et.agrees).read
      (n := 64) (r := 1) (by simp [Effect.components]) |>.trans cx1
  · exact (total6.trans et.agrees).mono (by simp [Effect.components])

end P256.Proofs.EcdhWrapper.Peer.Guards
