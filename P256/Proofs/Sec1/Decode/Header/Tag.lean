import P256.Proofs.Program.Code
import P256.Proofs.Common.Encoding.Parser.TagOps.Instructions
import P256.Proofs.Common.Encoding.Parser.ByteImmediate
import P256.Proofs.Common.Instructions.Setb.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Header

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Encoding.Parser P256.Proofs.Common.Encoding.Parser.TagOps
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

def validTag (tag : BitVec 8) : Bool :=
  tag == 0 || tag == 2 || tag == 3 || tag == 4 || tag == 5

private theorem bitmap (tag : BitVec 8) :
    (cmpSpec ((0x3d#8 >>> shiftCount 8 tag) &&&
      (if (cmpSpec (tag.setWidth 64) 6).CF then 1 else 0)) 1).ZF = validTag tag := by
  revert tag
  decide +kernel

theorem tag_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e4f7)
    (readable : MemReadable s (s.regValue .rsi) 1) :
    ∃ t, Advances boundary 8 s t ∧ ReadyToStep t ∧
      t.RIP = (if validTag (memLoad s.external (s.regValue .rsi) 8) then 0x10e514 else 0x10e68e) ∧
      t.regValue .rcx = (memLoad s.external (s.regValue .rsi) 8).setWidth 64 ∧
      AgreesExcept [.reg 0, .reg 1, .reg 8, .flags, .rip] s t := by
  have addZero : s.regValue .rsi + 0 = s.regValue .rsi := BitVec.add_zero _
  obtain ⟨s1, a1, r1, e1⟩ := (movzx_r32_m8_effect_step 0x10e4f7 1 (.base 6 .none) (by decide) rfl rfl).advances
    ready (programText_slice ((programLoaded_codeIn loaded))
      0xe4f7 _ (by decide) (by decide +kernel)) ⟨rip, by change MemReadable s (s.regValue .rsi + 0) 1; simpa only [addZero] using readable⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0xe4fa (by decide)))
  have g1 : AgreesExcept [.reg 1, .rip] s s1 := e1.agrees
  have total1 := g1
  have m1 : s1.external = s.external := total1.external (by simp [Component.Covers])
  have cx1 : s1.regValue .rcx = (memLoad s.external (s.regValue .rsi) 8).setWidth 64 := by
    have h : s1.regValue .rcx = (memLoad s.external (s.regValue .rsi + 0) 8).setWidth 64 := e1.writes
    simpa only [addZero] using h
  obtain ⟨s2, a2, r2, e2⟩ := (cmp_r64_imm8_effect_step 0x10e4fa 0x48 0xf9 6 (by simp [RexWPrefix]) rfl rfl).advances
    r1 (programText_slice ((programLoaded_codeIn loaded).of_external_eq m1)
      0xe4fa _ (by decide) (by decide +kernel)) e1.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe4fe (by decide)))
  have g2 : AgreesExcept [.flags, .rip] s1 s2 := e2.agrees
  have total2 := total1.trans g2
  have m2 : s2.external = s.external := total2.external (by simp [Component.Covers])
  have cf2 : (StatusFlags.ofRFLAGS s2.RFLAGS).CF =
      (cmpSpec ((memLoad s.external (s.regValue .rsi) 8).setWidth 64) 6).CF := by
    have h := e2.flags.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).CF = (cmpSpec (s1.regValue .rcx) 6).CF at h
    rwa [cx1] at h
  obtain ⟨s3, a3, r3, e3⟩ := (setcc_r8_effect_step 0x10e4fe 0x92 0xc0 (by simp [SupportedOpcode]) rfl (by decide)).advances
    r2 (programText_slice ((programLoaded_codeIn loaded).of_external_eq m2)
      0xe4fe _ (by decide) (by decide +kernel)) e2.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe501 (by decide)))
  have g3 : AgreesExcept [.reg 0, .rip] s2 s3 := e3.agrees
  have total3 := total2.trans g3
  have m3 : s3.external = s.external := total3.external (by simp [Component.Covers])
  have al3 : (Operand.reg 0 : Operand 8).read s3 =
      if (cmpSpec ((memLoad s.external (s.regValue .rsi) 8).setWidth 64) 6).CF then 1 else 0 := by
    have h := e3.writes
    change (Operand.reg 0 : Operand 64).read s3 = mergeGPR 8 _ _ at h
    change ((Operand.reg 0 : Operand 64).read s3).setWidth 8 = _
    rw [h, mergeGPR_low8]
    change (if (StatusFlags.ofRFLAGS s2.RFLAGS).CF then 1#8 else 0) = _
    rw [cf2]
    rfl
  obtain ⟨s4, a4, r4, e4⟩ := (mov_r8b_imm8_effect_step 0x10e501 0x3d).advances
    r3 (programText_slice ((programLoaded_codeIn loaded).of_external_eq m3)
      0xe501 _ (by decide) (by decide +kernel)) e3.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe504 (by decide)))
  have g4 : AgreesExcept [.reg 8, .rip] s3 s4 := by simpa [movR8bImm8Effect, Effect.components] using e4.agrees
  have total4 := total3.trans g4
  have m4 : s4.external = s.external := total4.external (by simp [Component.Covers])
  have byte4 : (Operand.reg 8 : Operand 8).read s4 = 0x3d := by
    have h := e4.writes
    change (Operand.reg 8 : Operand 64).read s4 = mergeGPR 8 _ _ at h
    change ((Operand.reg 8 : Operand 64).read s4).setWidth 8 = _
    rw [h, mergeGPR_low8]
    rfl
  obtain ⟨s5, a5, r5, e5⟩ := (shr_r8b_cl_effect_step 0x10e504).advances
    r4 (programText_slice ((programLoaded_codeIn loaded).of_external_eq m4)
      0xe504 _ (by decide) (by decide +kernel)) e4.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe507 (by decide)))
  have g5 : AgreesExcept [.reg 8, .flags, .rip] s4 s5 := by simpa [shrR8bClEffect, Effect.components] using e5.agrees
  have total5 := total4.trans g5
  have m5 : s5.external = s.external := total5.external (by simp [Component.Covers])
  have cx4 : (Operand.reg 1 : Operand 8).read s4 = memLoad s.external (s.regValue .rsi) 8 := by
    have h : s4.regValue .rcx = (memLoad s.external (s.regValue .rsi) 8).setWidth 64 :=
      (((g2.trans g3).trans g4).read (n := 64) (r := 1) (by simp)).trans cx1
    change (s4.regValue .rcx).setWidth 8 = _
    rw [h, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  have byte5 : (Operand.reg 8 : Operand 8).read s5 =
      0x3d#8 >>> shiftCount 8 (memLoad s.external (s.regValue .rsi) 8) := by
    have h := e5.writes
    change (Operand.reg 8 : Operand 64).read s5 = mergeGPR 8 _ _ at h
    change ((Operand.reg 8 : Operand 64).read s5).setWidth 8 = _
    rw [h, mergeGPR_low8, byte4, cx4]
    rfl
  obtain ⟨s6, a6, r6, e6⟩ := (and_r8b_al_effect_step 0x10e507).advances
    r5 (programText_slice ((programLoaded_codeIn loaded).of_external_eq m5)
      0xe507 _ (by decide) (by decide +kernel)) e5.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe50a (by decide)))
  have g6 : AgreesExcept [.reg 8, .flags, .rip] s5 s6 := by simpa [andR8bAlEffect, Effect.components] using e6.agrees
  have total6 := total5.trans g6
  have m6 : s6.external = s.external := total6.external (by simp [Component.Covers])
  have al5 := ((g4.trans g5).read (n := 8) (r := 0) (by simp)).trans al3
  have byte6 : (Operand.reg 8 : Operand 8).read s6 =
      (0x3d#8 >>> shiftCount 8 (memLoad s.external (s.regValue .rsi) 8)) &&&
        (if (cmpSpec ((memLoad s.external (s.regValue .rsi) 8).setWidth 64) 6).CF then 1 else 0) := by
    have h := e6.writes
    change (Operand.reg 8 : Operand 64).read s6 = mergeGPR 8 _ _ at h
    change ((Operand.reg 8 : Operand 64).read s6).setWidth 8 = _
    rw [h, mergeGPR_low8, byte5, al5]
  obtain ⟨s7, a7, r7, e7⟩ := (cmp_r8b_one_effect_step 0x10e50a).advances
    r6 (programText_slice ((programLoaded_codeIn loaded).of_external_eq m6)
      0xe50a _ (by decide) (by decide +kernel)) e6.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe50e (by decide)))
  have g7 : AgreesExcept [.flags, .rip] s6 s7 := by simpa [cmpR8bOneEffect, Effect.components] using e7.agrees
  have total7 := total6.trans g7
  have m7 : s7.external = s.external := total7.external (by simp [Component.Covers])
  have zf7 : (StatusFlags.ofRFLAGS s7.RFLAGS).ZF =
      validTag (memLoad s.external (s.regValue .rsi) 8) := by
    have h := e7.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s7.RFLAGS).ZF =
      (cmpSpec ((Operand.reg 8 : Operand 8).read s6) 1).ZF at h
    rw [byte6, bitmap] at h
    exact h
  have target : (jccEffect 0x10e50e 6 5 ((0x17a : BitVec 32).signExtend 64) s7).rip =
      if validTag (memLoad s.external (s.regValue .rsi) 8) then 0x10e514 else 0x10e68e := by
    simp only [jccEffect, branchEffect, branchTarget, condHolds, zf7]
    cases validTag (memLoad s.external (s.regValue .rsi) 8) <;> rfl
  obtain ⟨t, runT, rt, et⟩ := (jcc_rel32_effect_step 0x10e50e 5 0x17a).advances r7
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq m7)
      0xe50e _ (by decide) (by decide +kernel)) ⟨e7.rip, by intro; decide⟩
    (by rw [target]; split
        · exact boundary_ne_program outside (inProgram_of_textOffset 0xe514 (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0xe68e (by decide)))
  refine ⟨t, ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans runT,
    rt, et.rip.trans target, ?_, ?_⟩
  · exact (((((((g2.trans g3).trans g4).trans g5).trans g6).trans g7).trans et.agrees).read
      (n := 64) (r := 1) (by simp [jccEffect])).trans cx1
  · exact (total7.trans et.agrees).mono (by simp [jccEffect])

end P256.Proofs.Sec1.Decode.Header
