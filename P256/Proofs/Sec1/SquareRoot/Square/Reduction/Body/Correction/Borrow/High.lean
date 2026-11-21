import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow.Support

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow

open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.CrossPageStore
open P256.Proofs.Common.Field.Instructions
open P256.Proofs.Common.Field.FieldNeg.Instructions

set_option maxHeartbeats 800000 in
theorem high [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s t 32 112 112)
    (rip : t.RIP = 0x1136c0) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      ScalarFrame.FrameState s u 32 112 112 ∧ u.RIP = 0x1136fc ∧
      AgreesExcept (changes s [15, 5, 13, 0]) t u ∧
      u.regValue .r15 = (subWord (t.regValue .rax) (slot s t 32) (slot s t 8)) ∧
      u.regValue .rbp = -(borrow (t.regValue .rax) (slot s t 32) (subWord (t.regValue .rax) (slot s t 32) (slot s t 8))) := by
  have f0 := frame
  have g0r0 : ((Operand.reg 0 : Operand 64).read t) = t.regValue .rax := rfl
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (xor_r32_r32_rex_effect_step 0x1136c0 0x45 0xff (by simp [RexNoWPrefix]) (by decide)).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x136c0 _ (by decide) (by decide +kernel))
      rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136c3 (by decide)))
  change (xorR32R32Effect 0x1136c0 3 15 15 t).Holds t u1 at e1
  have f1 := f0.after_registers ready1 e1.agrees (by simp [xorR32R32Effect_components, Component.Covers]) (by simp [xorR32R32Effect_components])
  have g1r15 : ((Operand.reg 15 : Operand 64).read u1) = (0 : BitVec 64) := by
    have h := e1.writes
    simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, Write.AllHold] using h
  have load1 : slot s u1 8 = slot s t 8 := by
    change memLoad u1.external _ _ = _
    rw [show u1.external = t.external from e1.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])]
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (sub_r64_m64_effect_step 0x1136c3 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x136c3 _ (by decide) (by decide +kernel))
      ⟨e1.rip, (ScalarFrame.stack_writable pre.toCalleePre f1 (offset := 8) (len := 8) (by decide) (by decide) (by decide )).toMemReadable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136c8 (by decide)))
  change (subR64M64Effect 0x1136c3 15 (.sib 4 none 0 (.d8 8)) u1).Holds u1 u2 at e2
  have f2 := f1.after_registers ready2 e2.agrees (by simp [subR64M64Effect_components, Component.Covers]) (by simp [subR64M64Effect_components])
  have g2r15 : ((Operand.reg 15 : Operand 64).read u2) = ((0 : BitVec 64) - (slot s t 8)) := by
    have h := e2.writes
    change ((Operand.reg 15 : Operand 64).read u2) = ((Operand.reg 15 : Operand 64).read u1) - (memLoad u1.external (stackPtr u1 + 8) 64) at h
    rw [f1.rsp] at h
    change ((Operand.reg 15 : Operand 64).read u2) = ((Operand.reg 15 : Operand 64).read u1) - slot s u1 8 at h
    rw [g1r15, load1] at h
    exact h
  have g1r0 : ((Operand.reg 0 : Operand 64).read u1) = t.regValue .rax :=
    (e1.agrees.read (by simp [xorR32R32Effect_components])).trans g0r0
  have g2r0 : ((Operand.reg 0 : Operand 64).read u2) = t.regValue .rax :=
    (e2.agrees.read (by simp [subR64M64Effect_components])).trans g1r0
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (mov_r64_r64_effect_step 0x1136c8 0x48 0xc5 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x136c8 _ (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136cb (by decide)))
  change (movR64R64Effect 0x1136c8 5 0 u2).Holds u2 u3 at e3
  have f3 := f2.after_registers ready3 e3.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g3r5 : ((Operand.reg 5 : Operand 64).read u3) = t.regValue .rax := by
    have h := e3.writes
    change ((Operand.reg 5 : Operand 64).read u3) = ((Operand.reg 0 : Operand 64).read u2) at h
    rw [g2r0] at h
    exact h
  have load3 : slot s u3 32 = slot s t 32 := by
    change memLoad u3.external _ _ = _
    rw [show u3.external = t.external from ((e3.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans (e2.agrees.external (by simp [subR64M64Effect_components, Component.Covers]))).trans (e1.agrees.external (by simp [xorR32R32Effect_components, Component.Covers]))]
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (mov_r64_m64_effect_step 0x1136cb 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x136cb _ (by decide) (by decide +kernel))
      ⟨e3.rip, (ScalarFrame.stack_writable pre.toCalleePre f3 (offset := 32) (len := 8) (by decide) (by decide) (by decide )).toMemReadable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136d0 (by decide)))
  change (movR64M64Effect 0x1136cb 13 (.sib 4 none 0 (.d8 32)) u3).Holds u3 u4 at e4
  have f4 := f3.after_registers ready4 e4.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have g4r13 : ((Operand.reg 13 : Operand 64).read u4) = slot s t 32 := by
    have h := e4.writes
    change ((Operand.reg 13 : Operand 64).read u4) = memLoad u3.external (stackPtr u3 + 32) 64 at h
    rw [f3.rsp] at h
    change ((Operand.reg 13 : Operand 64).read u4) = slot s u3 32 at h
    rw [load3] at h
    exact h
  have g4r5 : ((Operand.reg 5 : Operand 64).read u4) = t.regValue .rax :=
    (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r5
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (sub_r64_r64_effect_step 0x1136d0 0x4c 0xed (by simp [RexWPrefix]) (by decide)).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x136d0 _ (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136d3 (by decide)))
  change (subR64R64Effect 0x1136d0 5 13 u4).Holds u4 u5 at e5
  have f5 := f4.after_registers ready5 e5.agrees (by simp [subR64R64Effect_components, Component.Covers]) (by simp [subR64R64Effect_components])
  have g5r5 : ((Operand.reg 5 : Operand 64).read u5) = (t.regValue .rax - slot s t 32) := by
    have h := e5.writes
    change ((Operand.reg 5 : Operand 64).read u5) = ((Operand.reg 5 : Operand 64).read u4) - ((Operand.reg 13 : Operand 64).read u4) at h
    rw [g4r13, g4r5] at h
    exact h
  have g3r15 : ((Operand.reg 15 : Operand 64).read u3) = ((0 : BitVec 64) - (slot s t 8)) :=
    (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r15
  have g4r15 : ((Operand.reg 15 : Operand 64).read u4) = ((0 : BitVec 64) - (slot s t 8)) :=
    (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r15
  have g5r15 : ((Operand.reg 15 : Operand 64).read u5) = ((0 : BitVec 64) - (slot s t 8)) :=
    (e5.agrees.read (by simp [subR64R64Effect_components])).trans g4r15
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (sar_r64_imm8_effect_step 0x1136d3 0x49 0xff 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x136d3 _ (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136d7 (by decide)))
  change (sarR64Effect 0x1136d3 4 15 63 u5).Holds u5 u6 at e6
  have f6 := f5.after_registers ready6 e6.agrees (by simp [sarR64Effect_components, Component.Covers]) (by simp [sarR64Effect_components])
  have g6r15 : ((Operand.reg 15 : Operand 64).read u6) = (((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 := by
    have h := e6.writes
    change ((Operand.reg 15 : Operand 64).read u6) = ((Operand.reg 15 : Operand 64).read u5).sshiftRight 63 at h
    rw [g5r15] at h
    exact h
  have g6r5 : ((Operand.reg 5 : Operand 64).read u6) = (t.regValue .rax - slot s t 32) :=
    (e6.agrees.read (by simp [sarR64Effect_components])).trans g5r5
  obtain ⟨u7, run7, ready7, e7⟩ :=
    (add_r64_r64_effect_step 0x1136d7 0x49 0xef (by simp [RexWPrefix]) (by decide)).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x136d7 _ (by decide) (by decide +kernel))
      e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136da (by decide)))
  change (addR64R64Effect 0x1136d7 15 5 u6).Holds u6 u7 at e7
  have f7 := f6.after_registers ready7 e7.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have g7r15 : ((Operand.reg 15 : Operand 64).read u7) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32)) := by
    have h := e7.writes
    change ((Operand.reg 15 : Operand 64).read u7) = ((Operand.reg 15 : Operand 64).read u6) + ((Operand.reg 5 : Operand 64).read u6) at h
    rw [g6r5, g6r15] at h
    exact h
  have g3r0 : ((Operand.reg 0 : Operand 64).read u3) = t.regValue .rax :=
    (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r0
  have g4r0 : ((Operand.reg 0 : Operand 64).read u4) = t.regValue .rax :=
    (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r0
  have g5r0 : ((Operand.reg 0 : Operand 64).read u5) = t.regValue .rax :=
    (e5.agrees.read (by simp [subR64R64Effect_components])).trans g4r0
  have g6r0 : ((Operand.reg 0 : Operand 64).read u6) = t.regValue .rax :=
    (e6.agrees.read (by simp [sarR64Effect_components])).trans g5r0
  have g7r0 : ((Operand.reg 0 : Operand 64).read u7) = t.regValue .rax :=
    (e7.agrees.read (by simp [addR64R64Effect_components])).trans g6r0
  obtain ⟨u8, run8, ready8, e8⟩ :=
    (not_r64_effect_step 0x1136da 0x48 0xd0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x136da _ (by decide) (by decide +kernel))
      e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136dd (by decide)))
  change (notR64Effect 0x1136da 0 u7).Holds u7 u8 at e8
  have f8 := f7.after_registers ready8 e8.agrees (by simp [notR64Effect_components, Component.Covers]) (by simp [notR64Effect_components])
  have g8r0 : ((Operand.reg 0 : Operand 64).read u8) = (~~~t.regValue .rax) := by
    have h := e8.writes
    change ((Operand.reg 0 : Operand 64).read u8) = ~~~((Operand.reg 0 : Operand 64).read u7) at h
    rw [g7r0] at h
    exact h
  have g5r13 : ((Operand.reg 13 : Operand 64).read u5) = slot s t 32 :=
    (e5.agrees.read (by simp [subR64R64Effect_components])).trans g4r13
  have g6r13 : ((Operand.reg 13 : Operand 64).read u6) = slot s t 32 :=
    (e6.agrees.read (by simp [sarR64Effect_components])).trans g5r13
  have g7r13 : ((Operand.reg 13 : Operand 64).read u7) = slot s t 32 :=
    (e7.agrees.read (by simp [addR64R64Effect_components])).trans g6r13
  have g8r13 : ((Operand.reg 13 : Operand 64).read u8) = slot s t 32 :=
    (e8.agrees.read (by simp [notR64Effect_components])).trans g7r13
  obtain ⟨u9, run9, ready9, e9⟩ :=
    (mov_r64_r64_effect_step 0x1136dd 0x4c 0xed (by simp [RexWPrefix]) (by decide)).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x136dd _ (by decide) (by decide +kernel))
      e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136e0 (by decide)))
  change (movR64R64Effect 0x1136dd 5 13 u8).Holds u8 u9 at e9
  have f9 := f8.after_registers ready9 e9.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g9r5 : ((Operand.reg 5 : Operand 64).read u9) = slot s t 32 := by
    have h := e9.writes
    change ((Operand.reg 5 : Operand 64).read u9) = ((Operand.reg 13 : Operand 64).read u8) at h
    rw [g8r13] at h
    exact h
  have g9r0 : ((Operand.reg 0 : Operand 64).read u9) = (~~~t.regValue .rax) :=
    (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r0
  obtain ⟨u10, run10, ready10, e10⟩ :=
    (and_r64_r64_effect_step 0x1136e0 0x48 0xc5 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x136e0 _ (by decide) (by decide +kernel))
      e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136e3 (by decide)))
  change (andR64R64Effect 0x1136e0 5 0 u9).Holds u9 u10 at e10
  have f10 := f9.after_registers ready10 e10.agrees (by simp [andR64R64Effect_components, Component.Covers]) (by simp [andR64R64Effect_components])
  have g10r5 : ((Operand.reg 5 : Operand 64).read u10) = (slot s t 32 &&& (~~~t.regValue .rax)) := by
    have h := e10.writes
    change ((Operand.reg 5 : Operand 64).read u10) = ((Operand.reg 5 : Operand 64).read u9) &&& ((Operand.reg 0 : Operand 64).read u9) at h
    rw [g9r0, g9r5] at h
    exact h
  have g9r13 : ((Operand.reg 13 : Operand 64).read u9) = slot s t 32 :=
    (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r13
  have g10r13 : ((Operand.reg 13 : Operand 64).read u10) = slot s t 32 :=
    (e10.agrees.read (by simp [andR64R64Effect_components])).trans g9r13
  have g10r0 : ((Operand.reg 0 : Operand 64).read u10) = (~~~t.regValue .rax) :=
    (e10.agrees.read (by simp [andR64R64Effect_components])).trans g9r0
  obtain ⟨u11, run11, ready11, e11⟩ :=
    (or_r64_r64_effect_step 0x1136e3 0x4c 0xe8 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x136e3 _ (by decide) (by decide +kernel))
      e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136e6 (by decide)))
  change (orR64R64Effect 0x1136e3 0 13 u10).Holds u10 u11 at e11
  have f11 := f10.after_registers ready11 e11.agrees (by simp [orR64R64Effect_components, Component.Covers]) (by simp [orR64R64Effect_components])
  have g11r0 : ((Operand.reg 0 : Operand 64).read u11) = ((~~~t.regValue .rax) ||| slot s t 32) := by
    have h := e11.writes
    change ((Operand.reg 0 : Operand 64).read u11) = ((Operand.reg 0 : Operand 64).read u10) ||| ((Operand.reg 13 : Operand 64).read u10) at h
    rw [g10r13, g10r0] at h
    exact h
  have g8r15 : ((Operand.reg 15 : Operand 64).read u8) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32)) :=
    (e8.agrees.read (by simp [notR64Effect_components])).trans g7r15
  have g9r15 : ((Operand.reg 15 : Operand 64).read u9) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32)) :=
    (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r15
  have g10r15 : ((Operand.reg 15 : Operand 64).read u10) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32)) :=
    (e10.agrees.read (by simp [andR64R64Effect_components])).trans g9r15
  have g11r15 : ((Operand.reg 15 : Operand 64).read u11) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32)) :=
    (e11.agrees.read (by simp [orR64R64Effect_components])).trans g10r15
  obtain ⟨u12, run12, ready12, e12⟩ :=
    (and_r64_r64_effect_step 0x1136e6 0x4c 0xf8 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f11.machine f11.bindingsSupported)
      (programText_slice (programLoaded_codeIn f11.loaded) 0x136e6 _ (by decide) (by decide +kernel))
      e11.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136e9 (by decide)))
  change (andR64R64Effect 0x1136e6 0 15 u11).Holds u11 u12 at e12
  have f12 := f11.after_registers ready12 e12.agrees (by simp [andR64R64Effect_components, Component.Covers]) (by simp [andR64R64Effect_components])
  have g12r0 : ((Operand.reg 0 : Operand 64).read u12) = (((~~~t.regValue .rax) ||| slot s t 32) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32))) := by
    have h := e12.writes
    change ((Operand.reg 0 : Operand 64).read u12) = ((Operand.reg 0 : Operand 64).read u11) &&& ((Operand.reg 15 : Operand 64).read u11) at h
    rw [g11r15, g11r0] at h
    exact h
  have g11r5 : ((Operand.reg 5 : Operand 64).read u11) = (slot s t 32 &&& (~~~t.regValue .rax)) :=
    (e11.agrees.read (by simp [orR64R64Effect_components])).trans g10r5
  have g12r5 : ((Operand.reg 5 : Operand 64).read u12) = (slot s t 32 &&& (~~~t.regValue .rax)) :=
    (e12.agrees.read (by simp [andR64R64Effect_components])).trans g11r5
  obtain ⟨u13, run13, ready13, e13⟩ :=
    (or_r64_r64_effect_step 0x1136e9 0x48 0xe8 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f12.machine f12.bindingsSupported)
      (programText_slice (programLoaded_codeIn f12.loaded) 0x136e9 _ (by decide) (by decide +kernel))
      e12.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136ec (by decide)))
  change (orR64R64Effect 0x1136e9 0 5 u12).Holds u12 u13 at e13
  have f13 := f12.after_registers ready13 e13.agrees (by simp [orR64R64Effect_components, Component.Covers]) (by simp [orR64R64Effect_components])
  have g13r0 : ((Operand.reg 0 : Operand 64).read u13) = ((((~~~t.regValue .rax) ||| slot s t 32) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32))) ||| (slot s t 32 &&& (~~~t.regValue .rax))) := by
    have h := e13.writes
    change ((Operand.reg 0 : Operand 64).read u13) = ((Operand.reg 0 : Operand 64).read u12) ||| ((Operand.reg 5 : Operand 64).read u12) at h
    rw [g12r5, g12r0] at h
    exact h
  obtain ⟨u14, run14, ready14, e14⟩ :=
    (shr_r64_imm8_effect_step 0x1136ec 0x48 0xe8 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f13.machine f13.bindingsSupported)
      (programText_slice (programLoaded_codeIn f13.loaded) 0x136ec _ (by decide) (by decide +kernel))
      e13.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136f0 (by decide)))
  change (shrR64Effect 0x1136ec 4 0 63 u13).Holds u13 u14 at e14
  have f14 := f13.after_registers ready14 e14.agrees (by simp [shrR64Effect_components, Component.Covers]) (by simp [shrR64Effect_components])
  have g14r0 : ((Operand.reg 0 : Operand 64).read u14) = (((((~~~t.regValue .rax) ||| slot s t 32) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32))) ||| (slot s t 32 &&& (~~~t.regValue .rax))) >>> 63) := by
    have h := e14.writes
    change ((Operand.reg 0 : Operand 64).read u14) = ((Operand.reg 0 : Operand 64).read u13) >>> 63 at h
    rw [g13r0] at h
    exact h
  obtain ⟨u15, run15, ready15, e15⟩ :=
    (mov_m64_r64_effect_step_any 0x1136f0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f14.machine f14.bindingsSupported)
      (programText_slice (programLoaded_codeIn f14.loaded) 0x136f0 _ (by decide) (by decide +kernel))
      ⟨e14.rip, ScalarFrame.stack_writable pre.toCalleePre f14 (offset := 8) (len := 8) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f14 (offset := 8) (len := 8) (codeOffset := 0x136f0) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136f5 (by decide)))
  change (movM64R64Effect 0x1136f0 0 (.sib 4 none 0 (.d8 8)) u14).Holds u14 u15 at e15
  have ag15 : AgreesExcept [.mem (stackPtr u14 + 8) 8, .rip] u14 u15 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e15.agrees
  have f15 := FirstRound.after_store pre f14 ready15 (offset := 8) (by decide) ag15
  have wr15 : slot s u15 8 = (((((~~~t.regValue .rax) ||| slot s t 32) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32))) ||| (slot s t 32 &&& (~~~t.regValue .rax))) >>> 63) := by
    have h := e15.writes
    change memLoad u15.external (stackPtr u14 + 8) 64 = ((Operand.reg 0 : Operand 64).read u14) at h
    rw [f14.rsp, g14r0] at h
    exact h
  obtain ⟨u16, run16, ready16, e16⟩ :=
    (xor_r32_r32_effect_step 0x1136f5 0xed (by decide)).advances (readyToStep f15.machine f15.bindingsSupported)
      (programText_slice (programLoaded_codeIn f15.loaded) 0x136f5 _ (by decide) (by decide +kernel))
      e15.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136f7 (by decide)))
  change (xorR32R32Effect 0x1136f5 2 5 5 u15).Holds u15 u16 at e16
  have f16 := f15.after_registers ready16 e16.agrees (by simp [xorR32R32Effect_components, Component.Covers]) (by simp [xorR32R32Effect_components])
  have g16r5 : ((Operand.reg 5 : Operand 64).read u16) = (0 : BitVec 64) := by
    have h := e16.writes
    simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, Write.AllHold] using h
  have load16 : slot s u16 8 = (((((~~~t.regValue .rax) ||| slot s t 32) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32))) ||| (slot s t 32 &&& (~~~t.regValue .rax))) >>> 63) := by
    change memLoad u16.external _ _ = _
    rw [show u16.external = u15.external from e16.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])]
    exact wr15
  obtain ⟨u17, run17, ready17, e17⟩ :=
    (sub_r64_m64_effect_step 0x1136f7 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f16.machine f16.bindingsSupported)
      (programText_slice (programLoaded_codeIn f16.loaded) 0x136f7 _ (by decide) (by decide +kernel))
      ⟨e16.rip, (ScalarFrame.stack_writable pre.toCalleePre f16 (offset := 8) (len := 8) (by decide) (by decide) (by decide )).toMemReadable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136fc (by decide)))
  change (subR64M64Effect 0x1136f7 5 (.sib 4 none 0 (.d8 8)) u16).Holds u16 u17 at e17
  have f17 := f16.after_registers ready17 e17.agrees (by simp [subR64M64Effect_components, Component.Covers]) (by simp [subR64M64Effect_components])
  have g17r5 : ((Operand.reg 5 : Operand 64).read u17) = ((0 : BitVec 64) - ((((((~~~t.regValue .rax) ||| slot s t 32) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32))) ||| (slot s t 32 &&& (~~~t.regValue .rax))) >>> 63))) := by
    have h := e17.writes
    change ((Operand.reg 5 : Operand 64).read u17) = ((Operand.reg 5 : Operand 64).read u16) - (memLoad u16.external (stackPtr u16 + 8) 64) at h
    rw [f16.rsp] at h
    change ((Operand.reg 5 : Operand 64).read u17) = ((Operand.reg 5 : Operand 64).read u16) - slot s u16 8 at h
    rw [g16r5, load16] at h
    exact h
  have g12r15 : ((Operand.reg 15 : Operand 64).read u12) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32)) :=
    (e12.agrees.read (by simp [andR64R64Effect_components])).trans g11r15
  have g13r15 : ((Operand.reg 15 : Operand 64).read u13) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32)) :=
    (e13.agrees.read (by simp [orR64R64Effect_components])).trans g12r15
  have g14r15 : ((Operand.reg 15 : Operand 64).read u14) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32)) :=
    (e14.agrees.read (by simp [shrR64Effect_components])).trans g13r15
  have g15r15 : ((Operand.reg 15 : Operand 64).read u15) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32)) :=
    (e15.agrees.read (by simp [movM64R64Effect_components])).trans g14r15
  have g16r15 : ((Operand.reg 15 : Operand 64).read u16) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32)) :=
    (e16.agrees.read (by simp [xorR32R32Effect_components])).trans g15r15
  have g17r15 : ((Operand.reg 15 : Operand 64).read u17) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rax - slot s t 32)) :=
    (e17.agrees.read (by simp [subR64M64Effect_components])).trans g16r15
  have ag : AgreesExcept (changes s [15, 5, 13, 0]) t u17 := ((((((((((((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans ag15).trans e16.agrees).trans e17.agrees).mono (by simp only [xorR32R32Effect_components, subR64M64Effect_components, movR64R64Effect_components, movR64M64Effect_components, subR64R64Effect_components, sarR64Effect_components, addR64R64Effect_components, notR64Effect_components, andR64R64Effect_components, orR64R64Effect_components, shrR64Effect_components, f14.rsp]; simp [changes])
  refine ⟨u17, ⟨17, ((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17)⟩, f17, e17.rip, ag, ?_, ?_⟩
  · change ((Operand.reg 15 : Operand 64).read u17) = _
    exact g17r15
  · change ((Operand.reg 5 : Operand 64).read u17) = _
    exact g17r5

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow
