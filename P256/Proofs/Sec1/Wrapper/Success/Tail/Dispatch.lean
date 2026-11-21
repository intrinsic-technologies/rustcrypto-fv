import P256.Proofs.HashToCurve.Wrapper.Finish.Immediate
import P256.Proofs.HashToCurve.Wrapper.Finish.Shift
import P256.Proofs.HashToCurve.Wrapper.Finish.Test
import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.Setb.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success.Tail

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.HashToCurve.Wrapper.Finish
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

theorem tag_dispatch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x101870)
    (readable : MemReadable s (stackPtr s) 1)
    (tag : memLoad s.external (stackPtr s) 8 = 0 ∨
      memLoad s.external (stackPtr s) 8 = 4) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ t.RIP = 0x1018af ∧
      t.regValue .rcx = (memLoad s.external (stackPtr s) 8).setWidth 64 ∧
      AgreesExcept [.reg 0, .reg 1, .reg 2, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, e1⟩ := (movzx_r32_m8_effect_step 0x101870 1
    (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x1870 _ (by decide) (by decide +kernel))
    ⟨rip, by change MemReadable s (stackPtr s + 0#64) 1; rw [BitVec.add_zero]; exact readable⟩ (boundary_ne_program outside (inProgram_of_textOffset 0x1874 (by decide)))
  have g1 : AgreesExcept [.reg 1, .rip] s s1 := e1.agrees
  have total1 := g1
  have m1 : s1.external = s.external := total1.external (by simp [Component.Covers])
  have cx1 : s1.regValue .rcx = (memLoad s.external (stackPtr s) 8).setWidth 64 := by
    have h : s1.regValue .rcx = (memLoad s.external (stackPtr s + 0#64) 8).setWidth 64 := e1.writes
    simpa only [BitVec.add_zero] using h
  obtain ⟨s2, a2, r2, e2⟩ := (cmp_r64_imm8_effect_step 0x101874 0x48 0xf9 6
    (by simp [RexWPrefix]) rfl rfl).advances r1
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m1)
      0x1874 _ (by decide) (by decide +kernel)) e1.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x1878 (by decide)))
  have g2 : AgreesExcept [.flags, .rip] s1 s2 := e2.agrees
  have total2 := total1.trans g2
  have m2 : s2.external = s.external := total2.external (by simp [Component.Covers])
  have cf2 : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = true := by
    have h := e2.flags.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).CF = (cmpSpec (s1.regValue .rcx) 6).CF at h
    rw [cx1] at h
    rcases tag with zero | four
    · rw [zero] at h
      exact h
    · rw [four] at h
      exact h
  obtain ⟨s3, a3, r3, e3⟩ := (setcc_r8_effect_step 0x101878 0x92 0xc0
    (by simp [SupportedOpcode]) rfl (by decide)).advances r2
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m2)
      0x1878 _ (by decide) (by decide +kernel)) e2.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x187b (by decide)))
  have g3 : AgreesExcept [.reg 0, .rip] s2 s3 := e3.agrees
  have total3 := total2.trans g3
  have m3 : s3.external = s.external := total3.external (by simp [Component.Covers])
  have al3 : (Operand.reg 0 : Operand 8).read s3 = 1 := by
    have h := e3.writes
    change (Operand.reg 0 : Operand 64).read s3 = mergeGPR 8 _ _ at h
    change ((Operand.reg 0 : Operand 64).read s3).setWidth 8 = _
    rw [h, mergeGPR_low8]
    change (if (StatusFlags.ofRFLAGS s2.RFLAGS).CF then 1#8 else 0) = _
    rw [cf2]
    rfl
  obtain ⟨s4, a4, r4, e4⟩ := (mov_dl_imm8_effect_step 0x10187b 0x3d).advances r3
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m3)
      0x187b _ (by decide) (by decide +kernel)) e3.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x187d (by decide)))
  have g4 : AgreesExcept [.reg 2, .rip] s3 s4 := e4.agrees
  have total4 := total3.trans g4
  have m4 : s4.external = s.external := total4.external (by simp [Component.Covers])
  have byte4 : (Operand.reg 2 : Operand 8).read s4 = 0x3d := by
    have h := e4.writes
    change (Operand.reg 2 : Operand 64).read s4 = mergeGPR 8 _ _ at h
    change ((Operand.reg 2 : Operand 64).read s4).setWidth 8 = _
    rw [h, mergeGPR_low8]
    rfl
  obtain ⟨s5, a5, r5, e5⟩ := (shr_dl_cl_effect_step 0x10187d).advances r4
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m4)
      0x187d _ (by decide) (by decide +kernel)) e4.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x187f (by decide)))
  have g5 : AgreesExcept [.reg 2, .flags, .rip] s4 s5 := by
    simpa [shrDlClEffect, Effect.components] using e5.agrees
  have total5 := total4.trans g5
  have m5 : s5.external = s.external := total5.external (by simp [Component.Covers])
  have cx4 : (Operand.reg 1 : Operand 8).read s4 = memLoad s.external (stackPtr s) 8 := by
    have h : s4.regValue .rcx = (memLoad s.external (stackPtr s) 8).setWidth 64 :=
      (((g2.trans g3).trans g4).read (n := 64) (r := 1) (by simp)).trans cx1
    change (s4.regValue .rcx).setWidth 8 = _
    rw [h, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  have byte5 : (Operand.reg 2 : Operand 8).read s5 =
      0x3d#8 >>> shiftCount 8 (memLoad s.external (stackPtr s) 8) := by
    have h := e5.writes
    change (Operand.reg 2 : Operand 64).read s5 = mergeGPR 8 _ _ at h
    change ((Operand.reg 2 : Operand 64).read s5).setWidth 8 = _
    rw [h, mergeGPR_low8, byte4, cx4]
    rfl
  obtain ⟨s6, a6, r6, e6⟩ := (test_al_dl_effect_step 0x10187f).advances r5
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m5)
      0x187f _ (by decide) (by decide +kernel)) e5.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x1881 (by decide)))
  have g6 : AgreesExcept [.flags, .rip] s5 s6 := e6.agrees
  have total6 := total5.trans g6
  have m6 : s6.external = s.external := total6.external (by simp [Component.Covers])
  have al5 := ((g4.trans g5).read (n := 8) (r := 0) (by simp)).trans al3
  have zf6 : (StatusFlags.ofRFLAGS s6.RFLAGS).ZF = false := by
    have h := e6.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s6.RFLAGS).ZF =
      (((Operand.reg 0 : Operand 8).read s5 &&& (Operand.reg 2 : Operand 8).read s5) == 0) at h
    rw [al5, byte5] at h
    rcases tag with zero | four
    · rw [zero] at h
      exact h
    · rw [four] at h
      exact h
  have target : (jccEffect 0x101881 2 5 ((0x2c : BitVec 8).signExtend 64) s6).rip = 0x1018af := by
    simp [jccEffect, branchEffect, branchTarget, condHolds, zf6]
  obtain ⟨t, runT, rt, et⟩ := (jcc_rel8_effect_step 0x101881 5 0x2c).advances r6
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m6)
      0x1881 _ (by decide) (by decide +kernel)) ⟨e6.rip, by intro; decide⟩
    (by rw [target]; exact boundary_ne_program outside (inProgram_of_textOffset 0x18af (by decide)))
  exact ⟨t, (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans runT,
    rt, et.rip.trans target,
    ((((((g2.trans g3).trans g4).trans g5).trans g6).trans et.agrees).read
      (n := 64) (r := 1) (by simp [jccEffect])).trans cx1,
    (total6.trans et.agrees).mono (by simp [jccEffect])⟩

end P256.Proofs.Sec1.Wrapper.Success.Tail
