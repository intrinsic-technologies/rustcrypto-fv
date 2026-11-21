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
theorem middleHigh [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s t 32 112 112)
    (rip : t.RIP = 0x113688) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      ScalarFrame.FrameState s u 32 112 112 ∧ u.RIP = 0x1136c0 ∧
      AgreesExcept (changes s [14, 15, 13, 5]) t u ∧
      u.regValue .r14 = (subWord (t.regValue .r8) (slot s t 40) (slot s t 8)) ∧
      slot s u 8 = borrow (t.regValue .r8) (slot s t 40) (subWord (t.regValue .r8) (slot s t 40) (slot s t 8)) := by
  have f0 := frame
  have g0r8 : ((Operand.reg 8 : Operand 64).read t) = t.regValue .r8 := rfl
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (xor_r32_r32_rex_effect_step 0x113688 0x45 0xf6 (by simp [RexNoWPrefix]) (by decide)).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x13688 _ (by decide) (by decide +kernel))
      rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1368b (by decide)))
  change (xorR32R32Effect 0x113688 3 14 14 t).Holds t u1 at e1
  have f1 := f0.after_registers ready1 e1.agrees (by simp [xorR32R32Effect_components, Component.Covers]) (by simp [xorR32R32Effect_components])
  have g1r14 : ((Operand.reg 14 : Operand 64).read u1) = (0 : BitVec 64) := by
    have h := e1.writes
    simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, Write.AllHold] using h
  have load1 : slot s u1 8 = slot s t 8 := by
    change memLoad u1.external _ _ = _
    rw [show u1.external = t.external from e1.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])]
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (sub_r64_m64_effect_step 0x11368b 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x1368b _ (by decide) (by decide +kernel))
      ⟨e1.rip, (ScalarFrame.stack_writable pre.toCalleePre f1 (offset := 8) (len := 8) (by decide) (by decide) (by decide )).toMemReadable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13690 (by decide)))
  change (subR64M64Effect 0x11368b 14 (.sib 4 none 0 (.d8 8)) u1).Holds u1 u2 at e2
  have f2 := f1.after_registers ready2 e2.agrees (by simp [subR64M64Effect_components, Component.Covers]) (by simp [subR64M64Effect_components])
  have g2r14 : ((Operand.reg 14 : Operand 64).read u2) = ((0 : BitVec 64) - (slot s t 8)) := by
    have h := e2.writes
    change ((Operand.reg 14 : Operand 64).read u2) = ((Operand.reg 14 : Operand 64).read u1) - (memLoad u1.external (stackPtr u1 + 8) 64) at h
    rw [f1.rsp] at h
    change ((Operand.reg 14 : Operand 64).read u2) = ((Operand.reg 14 : Operand 64).read u1) - slot s u1 8 at h
    rw [g1r14, load1] at h
    exact h
  have g1r8 : ((Operand.reg 8 : Operand 64).read u1) = t.regValue .r8 :=
    (e1.agrees.read (by simp [xorR32R32Effect_components])).trans g0r8
  have g2r8 : ((Operand.reg 8 : Operand 64).read u2) = t.regValue .r8 :=
    (e2.agrees.read (by simp [subR64M64Effect_components])).trans g1r8
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (mov_r64_r64_effect_step 0x113690 0x4d 0xc7 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x13690 _ (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13693 (by decide)))
  change (movR64R64Effect 0x113690 15 8 u2).Holds u2 u3 at e3
  have f3 := f2.after_registers ready3 e3.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g3r15 : ((Operand.reg 15 : Operand 64).read u3) = t.regValue .r8 := by
    have h := e3.writes
    change ((Operand.reg 15 : Operand 64).read u3) = ((Operand.reg 8 : Operand 64).read u2) at h
    rw [g2r8] at h
    exact h
  have load3 : slot s u3 40 = slot s t 40 := by
    change memLoad u3.external _ _ = _
    rw [show u3.external = t.external from ((e3.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans (e2.agrees.external (by simp [subR64M64Effect_components, Component.Covers]))).trans (e1.agrees.external (by simp [xorR32R32Effect_components, Component.Covers]))]
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (mov_r64_m64_effect_step 0x113693 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x13693 _ (by decide) (by decide +kernel))
      ⟨e3.rip, (ScalarFrame.stack_writable pre.toCalleePre f3 (offset := 40) (len := 8) (by decide) (by decide) (by decide )).toMemReadable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13698 (by decide)))
  change (movR64M64Effect 0x113693 13 (.sib 4 none 0 (.d8 40)) u3).Holds u3 u4 at e4
  have f4 := f3.after_registers ready4 e4.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have g4r13 : ((Operand.reg 13 : Operand 64).read u4) = slot s t 40 := by
    have h := e4.writes
    change ((Operand.reg 13 : Operand 64).read u4) = memLoad u3.external (stackPtr u3 + 40) 64 at h
    rw [f3.rsp] at h
    change ((Operand.reg 13 : Operand 64).read u4) = slot s u3 40 at h
    rw [load3] at h
    exact h
  have g4r15 : ((Operand.reg 15 : Operand 64).read u4) = t.regValue .r8 :=
    (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r15
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (sub_r64_r64_effect_step 0x113698 0x4d 0xef (by simp [RexWPrefix]) (by decide)).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x13698 _ (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1369b (by decide)))
  change (subR64R64Effect 0x113698 15 13 u4).Holds u4 u5 at e5
  have f5 := f4.after_registers ready5 e5.agrees (by simp [subR64R64Effect_components, Component.Covers]) (by simp [subR64R64Effect_components])
  have g5r15 : ((Operand.reg 15 : Operand 64).read u5) = (t.regValue .r8 - slot s t 40) := by
    have h := e5.writes
    change ((Operand.reg 15 : Operand 64).read u5) = ((Operand.reg 15 : Operand 64).read u4) - ((Operand.reg 13 : Operand 64).read u4) at h
    rw [g4r13, g4r15] at h
    exact h
  have g3r14 : ((Operand.reg 14 : Operand 64).read u3) = ((0 : BitVec 64) - (slot s t 8)) :=
    (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r14
  have g4r14 : ((Operand.reg 14 : Operand 64).read u4) = ((0 : BitVec 64) - (slot s t 8)) :=
    (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r14
  have g5r14 : ((Operand.reg 14 : Operand 64).read u5) = ((0 : BitVec 64) - (slot s t 8)) :=
    (e5.agrees.read (by simp [subR64R64Effect_components])).trans g4r14
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (sar_r64_imm8_effect_step 0x11369b 0x49 0xfe 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x1369b _ (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1369f (by decide)))
  change (sarR64Effect 0x11369b 4 14 63 u5).Holds u5 u6 at e6
  have f6 := f5.after_registers ready6 e6.agrees (by simp [sarR64Effect_components, Component.Covers]) (by simp [sarR64Effect_components])
  have g6r14 : ((Operand.reg 14 : Operand 64).read u6) = (((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 := by
    have h := e6.writes
    change ((Operand.reg 14 : Operand 64).read u6) = ((Operand.reg 14 : Operand 64).read u5).sshiftRight 63 at h
    rw [g5r14] at h
    exact h
  have g6r15 : ((Operand.reg 15 : Operand 64).read u6) = (t.regValue .r8 - slot s t 40) :=
    (e6.agrees.read (by simp [sarR64Effect_components])).trans g5r15
  obtain ⟨u7, run7, ready7, e7⟩ :=
    (add_r64_r64_effect_step 0x11369f 0x4d 0xfe (by simp [RexWPrefix]) (by decide)).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x1369f _ (by decide) (by decide +kernel))
      e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136a2 (by decide)))
  change (addR64R64Effect 0x11369f 14 15 u6).Holds u6 u7 at e7
  have f7 := f6.after_registers ready7 e7.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have g7r14 : ((Operand.reg 14 : Operand 64).read u7) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40)) := by
    have h := e7.writes
    change ((Operand.reg 14 : Operand 64).read u7) = ((Operand.reg 14 : Operand 64).read u6) + ((Operand.reg 15 : Operand 64).read u6) at h
    rw [g6r15, g6r14] at h
    exact h
  have g3r8 : ((Operand.reg 8 : Operand 64).read u3) = t.regValue .r8 :=
    (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r8
  have g4r8 : ((Operand.reg 8 : Operand 64).read u4) = t.regValue .r8 :=
    (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r8
  have g5r8 : ((Operand.reg 8 : Operand 64).read u5) = t.regValue .r8 :=
    (e5.agrees.read (by simp [subR64R64Effect_components])).trans g4r8
  have g6r8 : ((Operand.reg 8 : Operand 64).read u6) = t.regValue .r8 :=
    (e6.agrees.read (by simp [sarR64Effect_components])).trans g5r8
  have g7r8 : ((Operand.reg 8 : Operand 64).read u7) = t.regValue .r8 :=
    (e7.agrees.read (by simp [addR64R64Effect_components])).trans g6r8
  obtain ⟨u8, run8, ready8, e8⟩ :=
    (mov_r64_r64_effect_step 0x1136a2 0x4d 0xc7 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x136a2 _ (by decide) (by decide +kernel))
      e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136a5 (by decide)))
  change (movR64R64Effect 0x1136a2 15 8 u7).Holds u7 u8 at e8
  have f8 := f7.after_registers ready8 e8.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g8r15 : ((Operand.reg 15 : Operand 64).read u8) = t.regValue .r8 := by
    have h := e8.writes
    change ((Operand.reg 15 : Operand 64).read u8) = ((Operand.reg 8 : Operand 64).read u7) at h
    rw [g7r8] at h
    exact h
  obtain ⟨u9, run9, ready9, e9⟩ :=
    (not_r64_effect_step 0x1136a5 0x49 0xd7 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x136a5 _ (by decide) (by decide +kernel))
      e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136a8 (by decide)))
  change (notR64Effect 0x1136a5 15 u8).Holds u8 u9 at e9
  have f9 := f8.after_registers ready9 e9.agrees (by simp [notR64Effect_components, Component.Covers]) (by simp [notR64Effect_components])
  have g9r15 : ((Operand.reg 15 : Operand 64).read u9) = (~~~t.regValue .r8) := by
    have h := e9.writes
    change ((Operand.reg 15 : Operand 64).read u9) = ~~~((Operand.reg 15 : Operand 64).read u8) at h
    rw [g8r15] at h
    exact h
  have g5r13 : ((Operand.reg 13 : Operand 64).read u5) = slot s t 40 :=
    (e5.agrees.read (by simp [subR64R64Effect_components])).trans g4r13
  have g6r13 : ((Operand.reg 13 : Operand 64).read u6) = slot s t 40 :=
    (e6.agrees.read (by simp [sarR64Effect_components])).trans g5r13
  have g7r13 : ((Operand.reg 13 : Operand 64).read u7) = slot s t 40 :=
    (e7.agrees.read (by simp [addR64R64Effect_components])).trans g6r13
  have g8r13 : ((Operand.reg 13 : Operand 64).read u8) = slot s t 40 :=
    (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r13
  have g9r13 : ((Operand.reg 13 : Operand 64).read u9) = slot s t 40 :=
    (e9.agrees.read (by simp [notR64Effect_components])).trans g8r13
  obtain ⟨u10, run10, ready10, e10⟩ :=
    (mov_r64_r64_effect_step 0x1136a8 0x4c 0xed (by simp [RexWPrefix]) (by decide)).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x136a8 _ (by decide) (by decide +kernel))
      e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136ab (by decide)))
  change (movR64R64Effect 0x1136a8 5 13 u9).Holds u9 u10 at e10
  have f10 := f9.after_registers ready10 e10.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g10r5 : ((Operand.reg 5 : Operand 64).read u10) = slot s t 40 := by
    have h := e10.writes
    change ((Operand.reg 5 : Operand 64).read u10) = ((Operand.reg 13 : Operand 64).read u9) at h
    rw [g9r13] at h
    exact h
  have g10r15 : ((Operand.reg 15 : Operand 64).read u10) = (~~~t.regValue .r8) :=
    (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r15
  obtain ⟨u11, run11, ready11, e11⟩ :=
    (and_r64_r64_effect_step 0x1136ab 0x4c 0xfd (by simp [RexWPrefix]) (by decide)).advances (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x136ab _ (by decide) (by decide +kernel))
      e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136ae (by decide)))
  change (andR64R64Effect 0x1136ab 5 15 u10).Holds u10 u11 at e11
  have f11 := f10.after_registers ready11 e11.agrees (by simp [andR64R64Effect_components, Component.Covers]) (by simp [andR64R64Effect_components])
  have g11r5 : ((Operand.reg 5 : Operand 64).read u11) = (slot s t 40 &&& (~~~t.regValue .r8)) := by
    have h := e11.writes
    change ((Operand.reg 5 : Operand 64).read u11) = ((Operand.reg 5 : Operand 64).read u10) &&& ((Operand.reg 15 : Operand 64).read u10) at h
    rw [g10r15, g10r5] at h
    exact h
  have g10r13 : ((Operand.reg 13 : Operand 64).read u10) = slot s t 40 :=
    (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r13
  have g11r13 : ((Operand.reg 13 : Operand 64).read u11) = slot s t 40 :=
    (e11.agrees.read (by simp [andR64R64Effect_components])).trans g10r13
  have g11r15 : ((Operand.reg 15 : Operand 64).read u11) = (~~~t.regValue .r8) :=
    (e11.agrees.read (by simp [andR64R64Effect_components])).trans g10r15
  obtain ⟨u12, run12, ready12, e12⟩ :=
    (or_r64_r64_effect_step 0x1136ae 0x4d 0xef (by simp [RexWPrefix]) (by decide)).advances (readyToStep f11.machine f11.bindingsSupported)
      (programText_slice (programLoaded_codeIn f11.loaded) 0x136ae _ (by decide) (by decide +kernel))
      e11.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136b1 (by decide)))
  change (orR64R64Effect 0x1136ae 15 13 u11).Holds u11 u12 at e12
  have f12 := f11.after_registers ready12 e12.agrees (by simp [orR64R64Effect_components, Component.Covers]) (by simp [orR64R64Effect_components])
  have g12r15 : ((Operand.reg 15 : Operand 64).read u12) = ((~~~t.regValue .r8) ||| slot s t 40) := by
    have h := e12.writes
    change ((Operand.reg 15 : Operand 64).read u12) = ((Operand.reg 15 : Operand 64).read u11) ||| ((Operand.reg 13 : Operand 64).read u11) at h
    rw [g11r13, g11r15] at h
    exact h
  have g8r14 : ((Operand.reg 14 : Operand 64).read u8) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40)) :=
    (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r14
  have g9r14 : ((Operand.reg 14 : Operand 64).read u9) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40)) :=
    (e9.agrees.read (by simp [notR64Effect_components])).trans g8r14
  have g10r14 : ((Operand.reg 14 : Operand 64).read u10) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40)) :=
    (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r14
  have g11r14 : ((Operand.reg 14 : Operand 64).read u11) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40)) :=
    (e11.agrees.read (by simp [andR64R64Effect_components])).trans g10r14
  have g12r14 : ((Operand.reg 14 : Operand 64).read u12) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40)) :=
    (e12.agrees.read (by simp [orR64R64Effect_components])).trans g11r14
  obtain ⟨u13, run13, ready13, e13⟩ :=
    (and_r64_r64_effect_step 0x1136b1 0x4d 0xf7 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f12.machine f12.bindingsSupported)
      (programText_slice (programLoaded_codeIn f12.loaded) 0x136b1 _ (by decide) (by decide +kernel))
      e12.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136b4 (by decide)))
  change (andR64R64Effect 0x1136b1 15 14 u12).Holds u12 u13 at e13
  have f13 := f12.after_registers ready13 e13.agrees (by simp [andR64R64Effect_components, Component.Covers]) (by simp [andR64R64Effect_components])
  have g13r15 : ((Operand.reg 15 : Operand 64).read u13) = (((~~~t.regValue .r8) ||| slot s t 40) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40))) := by
    have h := e13.writes
    change ((Operand.reg 15 : Operand 64).read u13) = ((Operand.reg 15 : Operand 64).read u12) &&& ((Operand.reg 14 : Operand 64).read u12) at h
    rw [g12r14, g12r15] at h
    exact h
  have g12r5 : ((Operand.reg 5 : Operand 64).read u12) = (slot s t 40 &&& (~~~t.regValue .r8)) :=
    (e12.agrees.read (by simp [orR64R64Effect_components])).trans g11r5
  have g13r5 : ((Operand.reg 5 : Operand 64).read u13) = (slot s t 40 &&& (~~~t.regValue .r8)) :=
    (e13.agrees.read (by simp [andR64R64Effect_components])).trans g12r5
  obtain ⟨u14, run14, ready14, e14⟩ :=
    (or_r64_r64_effect_step 0x1136b4 0x49 0xef (by simp [RexWPrefix]) (by decide)).advances (readyToStep f13.machine f13.bindingsSupported)
      (programText_slice (programLoaded_codeIn f13.loaded) 0x136b4 _ (by decide) (by decide +kernel))
      e13.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136b7 (by decide)))
  change (orR64R64Effect 0x1136b4 15 5 u13).Holds u13 u14 at e14
  have f14 := f13.after_registers ready14 e14.agrees (by simp [orR64R64Effect_components, Component.Covers]) (by simp [orR64R64Effect_components])
  have g14r15 : ((Operand.reg 15 : Operand 64).read u14) = ((((~~~t.regValue .r8) ||| slot s t 40) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40))) ||| (slot s t 40 &&& (~~~t.regValue .r8))) := by
    have h := e14.writes
    change ((Operand.reg 15 : Operand 64).read u14) = ((Operand.reg 15 : Operand 64).read u13) ||| ((Operand.reg 5 : Operand 64).read u13) at h
    rw [g13r5, g13r15] at h
    exact h
  obtain ⟨u15, run15, ready15, e15⟩ :=
    (shr_r64_imm8_effect_step 0x1136b7 0x49 0xef 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f14.machine f14.bindingsSupported)
      (programText_slice (programLoaded_codeIn f14.loaded) 0x136b7 _ (by decide) (by decide +kernel))
      e14.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136bb (by decide)))
  change (shrR64Effect 0x1136b7 4 15 63 u14).Holds u14 u15 at e15
  have f15 := f14.after_registers ready15 e15.agrees (by simp [shrR64Effect_components, Component.Covers]) (by simp [shrR64Effect_components])
  have g15r15 : ((Operand.reg 15 : Operand 64).read u15) = (((((~~~t.regValue .r8) ||| slot s t 40) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40))) ||| (slot s t 40 &&& (~~~t.regValue .r8))) >>> 63) := by
    have h := e15.writes
    change ((Operand.reg 15 : Operand 64).read u15) = ((Operand.reg 15 : Operand 64).read u14) >>> 63 at h
    rw [g14r15] at h
    exact h
  obtain ⟨u16, run16, ready16, e16⟩ :=
    (mov_m64_r64_effect_step_any 0x1136bb 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f15.machine f15.bindingsSupported)
      (programText_slice (programLoaded_codeIn f15.loaded) 0x136bb _ (by decide) (by decide +kernel))
      ⟨e15.rip, ScalarFrame.stack_writable pre.toCalleePre f15 (offset := 8) (len := 8) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f15 (offset := 8) (len := 8) (codeOffset := 0x136bb) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136c0 (by decide)))
  change (movM64R64Effect 0x1136bb 15 (.sib 4 none 0 (.d8 8)) u15).Holds u15 u16 at e16
  have ag16 : AgreesExcept [.mem (stackPtr u15 + 8) 8, .rip] u15 u16 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e16.agrees
  have f16 := FirstRound.after_store pre f15 ready16 (offset := 8) (by decide) ag16
  have wr16 : slot s u16 8 = (((((~~~t.regValue .r8) ||| slot s t 40) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40))) ||| (slot s t 40 &&& (~~~t.regValue .r8))) >>> 63) := by
    have h := e16.writes
    change memLoad u16.external (stackPtr u15 + 8) 64 = ((Operand.reg 15 : Operand 64).read u15) at h
    rw [f15.rsp, g15r15] at h
    exact h
  have g13r14 : ((Operand.reg 14 : Operand 64).read u13) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40)) :=
    (e13.agrees.read (by simp [andR64R64Effect_components])).trans g12r14
  have g14r14 : ((Operand.reg 14 : Operand 64).read u14) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40)) :=
    (e14.agrees.read (by simp [orR64R64Effect_components])).trans g13r14
  have g15r14 : ((Operand.reg 14 : Operand 64).read u15) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40)) :=
    (e15.agrees.read (by simp [shrR64Effect_components])).trans g14r14
  have g16r14 : ((Operand.reg 14 : Operand 64).read u16) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .r8 - slot s t 40)) :=
    (e16.agrees.read (by simp [movM64R64Effect_components])).trans g15r14
  have ag : AgreesExcept (changes s [14, 15, 13, 5]) t u16 := (((((((((((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans ag16).mono (by simp only [xorR32R32Effect_components, subR64M64Effect_components, movR64R64Effect_components, movR64M64Effect_components, subR64R64Effect_components, sarR64Effect_components, addR64R64Effect_components, notR64Effect_components, andR64R64Effect_components, orR64R64Effect_components, shrR64Effect_components, f15.rsp]; simp [changes])
  refine ⟨u16, ⟨16, (((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16)⟩, f16, e16.rip, ag, ?_, ?_⟩
  · change ((Operand.reg 14 : Operand 64).read u16) = _
    exact g16r14
  · exact wr16

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow
