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
theorem middleLow [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s t 32 112 112)
    (rip : t.RIP = 0x11364b) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      ScalarFrame.FrameState s u 32 112 112 ∧ u.RIP = 0x113688 ∧
      AgreesExcept (changes s [10, 9, 14, 13, 15]) t u ∧
      u.regValue .r9 = (subWord (t.regValue .rcx) (slot s t 48) (slot s t 8)) ∧
      slot s u 8 = borrow (t.regValue .rcx) (slot s t 48) (subWord (t.regValue .rcx) (slot s t 48) (slot s t 8)) := by
  have f0 := frame
  have g0r1 : ((Operand.reg 1 : Operand 64).read t) = t.regValue .rcx := rfl
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (lea_r64_effect_step 0x11364b 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x1364b _ (by decide) (by decide +kernel))
      rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13650 (by decide)))
  change (leaR64Effect 0x11364b 10 (.sib 4 none 0 (.d8 8)) t).Holds t u1 at e1
  have f1 := f0.after_registers ready1 e1.agrees (by simp [leaR64Effect_components, Component.Covers]) (by simp [leaR64Effect_components])
  have g1r10 : ((Operand.reg 10 : Operand 64).read u1) = (stackPtr s - 112 + 8) := by
    have h := e1.writes
    change ((Operand.reg 10 : Operand 64).read u1) = stackPtr t + 8 at h
    rw [f0.rsp] at h
    exact h
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (xor_r32_r32_rex_effect_step 0x113650 0x45 0xc9 (by simp [RexNoWPrefix]) (by decide)).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x13650 _ (by decide) (by decide +kernel))
      e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13653 (by decide)))
  change (xorR32R32Effect 0x113650 3 9 9 u1).Holds u1 u2 at e2
  have f2 := f1.after_registers ready2 e2.agrees (by simp [xorR32R32Effect_components, Component.Covers]) (by simp [xorR32R32Effect_components])
  have g2r9 : ((Operand.reg 9 : Operand 64).read u2) = (0 : BitVec 64) := by
    have h := e2.writes
    simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, Write.AllHold] using h
  have load2 : slot s u2 8 = slot s t 8 := by
    change memLoad u2.external _ _ = _
    rw [show u2.external = t.external from (e2.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])).trans (e1.agrees.external (by simp [leaR64Effect_components, Component.Covers]))]
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (sub_r64_m64_effect_step 0x113653 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x13653 _ (by decide) (by decide +kernel))
      ⟨e2.rip, (ScalarFrame.stack_writable pre.toCalleePre f2 (offset := 8) (len := 8) (by decide) (by decide) (by decide )).toMemReadable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13658 (by decide)))
  change (subR64M64Effect 0x113653 9 (.sib 4 none 0 (.d8 8)) u2).Holds u2 u3 at e3
  have f3 := f2.after_registers ready3 e3.agrees (by simp [subR64M64Effect_components, Component.Covers]) (by simp [subR64M64Effect_components])
  have g3r9 : ((Operand.reg 9 : Operand 64).read u3) = ((0 : BitVec 64) - (slot s t 8)) := by
    have h := e3.writes
    change ((Operand.reg 9 : Operand 64).read u3) = ((Operand.reg 9 : Operand 64).read u2) - (memLoad u2.external (stackPtr u2 + 8) 64) at h
    rw [f2.rsp] at h
    change ((Operand.reg 9 : Operand 64).read u3) = ((Operand.reg 9 : Operand 64).read u2) - slot s u2 8 at h
    rw [g2r9, load2] at h
    exact h
  have g1r1 : ((Operand.reg 1 : Operand 64).read u1) = t.regValue .rcx :=
    (e1.agrees.read (by simp [leaR64Effect_components])).trans g0r1
  have g2r1 : ((Operand.reg 1 : Operand 64).read u2) = t.regValue .rcx :=
    (e2.agrees.read (by simp [xorR32R32Effect_components])).trans g1r1
  have g3r1 : ((Operand.reg 1 : Operand 64).read u3) = t.regValue .rcx :=
    (e3.agrees.read (by simp [subR64M64Effect_components])).trans g2r1
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (mov_r64_r64_effect_step 0x113658 0x49 0xce (by simp [RexWPrefix]) (by decide)).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x13658 _ (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1365b (by decide)))
  change (movR64R64Effect 0x113658 14 1 u3).Holds u3 u4 at e4
  have f4 := f3.after_registers ready4 e4.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g4r14 : ((Operand.reg 14 : Operand 64).read u4) = t.regValue .rcx := by
    have h := e4.writes
    change ((Operand.reg 14 : Operand 64).read u4) = ((Operand.reg 1 : Operand 64).read u3) at h
    rw [g3r1] at h
    exact h
  have load4 : slot s u4 48 = slot s t 48 := by
    change memLoad u4.external _ _ = _
    rw [show u4.external = t.external from (((e4.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans (e3.agrees.external (by simp [subR64M64Effect_components, Component.Covers]))).trans (e2.agrees.external (by simp [xorR32R32Effect_components, Component.Covers]))).trans (e1.agrees.external (by simp [leaR64Effect_components, Component.Covers]))]
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (mov_r64_m64_effect_step 0x11365b 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x1365b _ (by decide) (by decide +kernel))
      ⟨e4.rip, (ScalarFrame.stack_writable pre.toCalleePre f4 (offset := 48) (len := 8) (by decide) (by decide) (by decide )).toMemReadable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13660 (by decide)))
  change (movR64M64Effect 0x11365b 13 (.sib 4 none 0 (.d8 48)) u4).Holds u4 u5 at e5
  have f5 := f4.after_registers ready5 e5.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have g5r13 : ((Operand.reg 13 : Operand 64).read u5) = slot s t 48 := by
    have h := e5.writes
    change ((Operand.reg 13 : Operand 64).read u5) = memLoad u4.external (stackPtr u4 + 48) 64 at h
    rw [f4.rsp] at h
    change ((Operand.reg 13 : Operand 64).read u5) = slot s u4 48 at h
    rw [load4] at h
    exact h
  have g5r14 : ((Operand.reg 14 : Operand 64).read u5) = t.regValue .rcx :=
    (e5.agrees.read (by simp [movR64M64Effect_components])).trans g4r14
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (sub_r64_r64_effect_step 0x113660 0x4d 0xee (by simp [RexWPrefix]) (by decide)).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x13660 _ (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13663 (by decide)))
  change (subR64R64Effect 0x113660 14 13 u5).Holds u5 u6 at e6
  have f6 := f5.after_registers ready6 e6.agrees (by simp [subR64R64Effect_components, Component.Covers]) (by simp [subR64R64Effect_components])
  have g6r14 : ((Operand.reg 14 : Operand 64).read u6) = (t.regValue .rcx - slot s t 48) := by
    have h := e6.writes
    change ((Operand.reg 14 : Operand 64).read u6) = ((Operand.reg 14 : Operand 64).read u5) - ((Operand.reg 13 : Operand 64).read u5) at h
    rw [g5r13, g5r14] at h
    exact h
  have g4r9 : ((Operand.reg 9 : Operand 64).read u4) = ((0 : BitVec 64) - (slot s t 8)) :=
    (e4.agrees.read (by simp [movR64R64Effect_components])).trans g3r9
  have g5r9 : ((Operand.reg 9 : Operand 64).read u5) = ((0 : BitVec 64) - (slot s t 8)) :=
    (e5.agrees.read (by simp [movR64M64Effect_components])).trans g4r9
  have g6r9 : ((Operand.reg 9 : Operand 64).read u6) = ((0 : BitVec 64) - (slot s t 8)) :=
    (e6.agrees.read (by simp [subR64R64Effect_components])).trans g5r9
  obtain ⟨u7, run7, ready7, e7⟩ :=
    (sar_r64_imm8_effect_step 0x113663 0x49 0xf9 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x13663 _ (by decide) (by decide +kernel))
      e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13667 (by decide)))
  change (sarR64Effect 0x113663 4 9 63 u6).Holds u6 u7 at e7
  have f7 := f6.after_registers ready7 e7.agrees (by simp [sarR64Effect_components, Component.Covers]) (by simp [sarR64Effect_components])
  have g7r9 : ((Operand.reg 9 : Operand 64).read u7) = (((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 := by
    have h := e7.writes
    change ((Operand.reg 9 : Operand 64).read u7) = ((Operand.reg 9 : Operand 64).read u6).sshiftRight 63 at h
    rw [g6r9] at h
    exact h
  have g7r14 : ((Operand.reg 14 : Operand 64).read u7) = (t.regValue .rcx - slot s t 48) :=
    (e7.agrees.read (by simp [sarR64Effect_components])).trans g6r14
  obtain ⟨u8, run8, ready8, e8⟩ :=
    (add_r64_r64_effect_step 0x113667 0x4d 0xf1 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x13667 _ (by decide) (by decide +kernel))
      e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1366a (by decide)))
  change (addR64R64Effect 0x113667 9 14 u7).Holds u7 u8 at e8
  have f8 := f7.after_registers ready8 e8.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have g8r9 : ((Operand.reg 9 : Operand 64).read u8) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48)) := by
    have h := e8.writes
    change ((Operand.reg 9 : Operand 64).read u8) = ((Operand.reg 9 : Operand 64).read u7) + ((Operand.reg 14 : Operand 64).read u7) at h
    rw [g7r14, g7r9] at h
    exact h
  have g4r1 : ((Operand.reg 1 : Operand 64).read u4) = t.regValue .rcx :=
    (e4.agrees.read (by simp [movR64R64Effect_components])).trans g3r1
  have g5r1 : ((Operand.reg 1 : Operand 64).read u5) = t.regValue .rcx :=
    (e5.agrees.read (by simp [movR64M64Effect_components])).trans g4r1
  have g6r1 : ((Operand.reg 1 : Operand 64).read u6) = t.regValue .rcx :=
    (e6.agrees.read (by simp [subR64R64Effect_components])).trans g5r1
  have g7r1 : ((Operand.reg 1 : Operand 64).read u7) = t.regValue .rcx :=
    (e7.agrees.read (by simp [sarR64Effect_components])).trans g6r1
  have g8r1 : ((Operand.reg 1 : Operand 64).read u8) = t.regValue .rcx :=
    (e8.agrees.read (by simp [addR64R64Effect_components])).trans g7r1
  obtain ⟨u9, run9, ready9, e9⟩ :=
    (mov_r64_r64_effect_step 0x11366a 0x49 0xce (by simp [RexWPrefix]) (by decide)).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x1366a _ (by decide) (by decide +kernel))
      e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1366d (by decide)))
  change (movR64R64Effect 0x11366a 14 1 u8).Holds u8 u9 at e9
  have f9 := f8.after_registers ready9 e9.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g9r14 : ((Operand.reg 14 : Operand 64).read u9) = t.regValue .rcx := by
    have h := e9.writes
    change ((Operand.reg 14 : Operand 64).read u9) = ((Operand.reg 1 : Operand 64).read u8) at h
    rw [g8r1] at h
    exact h
  obtain ⟨u10, run10, ready10, e10⟩ :=
    (not_r64_effect_step 0x11366d 0x49 0xd6 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x1366d _ (by decide) (by decide +kernel))
      e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13670 (by decide)))
  change (notR64Effect 0x11366d 14 u9).Holds u9 u10 at e10
  have f10 := f9.after_registers ready10 e10.agrees (by simp [notR64Effect_components, Component.Covers]) (by simp [notR64Effect_components])
  have g10r14 : ((Operand.reg 14 : Operand 64).read u10) = (~~~t.regValue .rcx) := by
    have h := e10.writes
    change ((Operand.reg 14 : Operand 64).read u10) = ~~~((Operand.reg 14 : Operand 64).read u9) at h
    rw [g9r14] at h
    exact h
  have g6r13 : ((Operand.reg 13 : Operand 64).read u6) = slot s t 48 :=
    (e6.agrees.read (by simp [subR64R64Effect_components])).trans g5r13
  have g7r13 : ((Operand.reg 13 : Operand 64).read u7) = slot s t 48 :=
    (e7.agrees.read (by simp [sarR64Effect_components])).trans g6r13
  have g8r13 : ((Operand.reg 13 : Operand 64).read u8) = slot s t 48 :=
    (e8.agrees.read (by simp [addR64R64Effect_components])).trans g7r13
  have g9r13 : ((Operand.reg 13 : Operand 64).read u9) = slot s t 48 :=
    (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r13
  have g10r13 : ((Operand.reg 13 : Operand 64).read u10) = slot s t 48 :=
    (e10.agrees.read (by simp [notR64Effect_components])).trans g9r13
  obtain ⟨u11, run11, ready11, e11⟩ :=
    (mov_r64_r64_effect_step 0x113670 0x4d 0xef (by simp [RexWPrefix]) (by decide)).advances (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x13670 _ (by decide) (by decide +kernel))
      e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13673 (by decide)))
  change (movR64R64Effect 0x113670 15 13 u10).Holds u10 u11 at e11
  have f11 := f10.after_registers ready11 e11.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g11r15 : ((Operand.reg 15 : Operand 64).read u11) = slot s t 48 := by
    have h := e11.writes
    change ((Operand.reg 15 : Operand 64).read u11) = ((Operand.reg 13 : Operand 64).read u10) at h
    rw [g10r13] at h
    exact h
  have g11r14 : ((Operand.reg 14 : Operand 64).read u11) = (~~~t.regValue .rcx) :=
    (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r14
  obtain ⟨u12, run12, ready12, e12⟩ :=
    (and_r64_r64_effect_step 0x113673 0x4d 0xf7 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f11.machine f11.bindingsSupported)
      (programText_slice (programLoaded_codeIn f11.loaded) 0x13673 _ (by decide) (by decide +kernel))
      e11.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13676 (by decide)))
  change (andR64R64Effect 0x113673 15 14 u11).Holds u11 u12 at e12
  have f12 := f11.after_registers ready12 e12.agrees (by simp [andR64R64Effect_components, Component.Covers]) (by simp [andR64R64Effect_components])
  have g12r15 : ((Operand.reg 15 : Operand 64).read u12) = (slot s t 48 &&& (~~~t.regValue .rcx)) := by
    have h := e12.writes
    change ((Operand.reg 15 : Operand 64).read u12) = ((Operand.reg 15 : Operand 64).read u11) &&& ((Operand.reg 14 : Operand 64).read u11) at h
    rw [g11r14, g11r15] at h
    exact h
  have g11r13 : ((Operand.reg 13 : Operand 64).read u11) = slot s t 48 :=
    (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r13
  have g12r13 : ((Operand.reg 13 : Operand 64).read u12) = slot s t 48 :=
    (e12.agrees.read (by simp [andR64R64Effect_components])).trans g11r13
  have g12r14 : ((Operand.reg 14 : Operand 64).read u12) = (~~~t.regValue .rcx) :=
    (e12.agrees.read (by simp [andR64R64Effect_components])).trans g11r14
  obtain ⟨u13, run13, ready13, e13⟩ :=
    (or_r64_r64_effect_step 0x113676 0x4d 0xee (by simp [RexWPrefix]) (by decide)).advances (readyToStep f12.machine f12.bindingsSupported)
      (programText_slice (programLoaded_codeIn f12.loaded) 0x13676 _ (by decide) (by decide +kernel))
      e12.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13679 (by decide)))
  change (orR64R64Effect 0x113676 14 13 u12).Holds u12 u13 at e13
  have f13 := f12.after_registers ready13 e13.agrees (by simp [orR64R64Effect_components, Component.Covers]) (by simp [orR64R64Effect_components])
  have g13r14 : ((Operand.reg 14 : Operand 64).read u13) = ((~~~t.regValue .rcx) ||| slot s t 48) := by
    have h := e13.writes
    change ((Operand.reg 14 : Operand 64).read u13) = ((Operand.reg 14 : Operand 64).read u12) ||| ((Operand.reg 13 : Operand 64).read u12) at h
    rw [g12r13, g12r14] at h
    exact h
  have g9r9 : ((Operand.reg 9 : Operand 64).read u9) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48)) :=
    (e9.agrees.read (by simp [movR64R64Effect_components])).trans g8r9
  have g10r9 : ((Operand.reg 9 : Operand 64).read u10) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48)) :=
    (e10.agrees.read (by simp [notR64Effect_components])).trans g9r9
  have g11r9 : ((Operand.reg 9 : Operand 64).read u11) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48)) :=
    (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r9
  have g12r9 : ((Operand.reg 9 : Operand 64).read u12) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48)) :=
    (e12.agrees.read (by simp [andR64R64Effect_components])).trans g11r9
  have g13r9 : ((Operand.reg 9 : Operand 64).read u13) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48)) :=
    (e13.agrees.read (by simp [orR64R64Effect_components])).trans g12r9
  obtain ⟨u14, run14, ready14, e14⟩ :=
    (and_r64_r64_effect_step 0x113679 0x4d 0xce (by simp [RexWPrefix]) (by decide)).advances (readyToStep f13.machine f13.bindingsSupported)
      (programText_slice (programLoaded_codeIn f13.loaded) 0x13679 _ (by decide) (by decide +kernel))
      e13.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1367c (by decide)))
  change (andR64R64Effect 0x113679 14 9 u13).Holds u13 u14 at e14
  have f14 := f13.after_registers ready14 e14.agrees (by simp [andR64R64Effect_components, Component.Covers]) (by simp [andR64R64Effect_components])
  have g14r14 : ((Operand.reg 14 : Operand 64).read u14) = (((~~~t.regValue .rcx) ||| slot s t 48) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48))) := by
    have h := e14.writes
    change ((Operand.reg 14 : Operand 64).read u14) = ((Operand.reg 14 : Operand 64).read u13) &&& ((Operand.reg 9 : Operand 64).read u13) at h
    rw [g13r9, g13r14] at h
    exact h
  have g13r15 : ((Operand.reg 15 : Operand 64).read u13) = (slot s t 48 &&& (~~~t.regValue .rcx)) :=
    (e13.agrees.read (by simp [orR64R64Effect_components])).trans g12r15
  have g14r15 : ((Operand.reg 15 : Operand 64).read u14) = (slot s t 48 &&& (~~~t.regValue .rcx)) :=
    (e14.agrees.read (by simp [andR64R64Effect_components])).trans g13r15
  obtain ⟨u15, run15, ready15, e15⟩ :=
    (or_r64_r64_effect_step 0x11367c 0x4d 0xfe (by simp [RexWPrefix]) (by decide)).advances (readyToStep f14.machine f14.bindingsSupported)
      (programText_slice (programLoaded_codeIn f14.loaded) 0x1367c _ (by decide) (by decide +kernel))
      e14.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1367f (by decide)))
  change (orR64R64Effect 0x11367c 14 15 u14).Holds u14 u15 at e15
  have f15 := f14.after_registers ready15 e15.agrees (by simp [orR64R64Effect_components, Component.Covers]) (by simp [orR64R64Effect_components])
  have g15r14 : ((Operand.reg 14 : Operand 64).read u15) = ((((~~~t.regValue .rcx) ||| slot s t 48) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48))) ||| (slot s t 48 &&& (~~~t.regValue .rcx))) := by
    have h := e15.writes
    change ((Operand.reg 14 : Operand 64).read u15) = ((Operand.reg 14 : Operand 64).read u14) ||| ((Operand.reg 15 : Operand 64).read u14) at h
    rw [g14r15, g14r14] at h
    exact h
  obtain ⟨u16, run16, ready16, e16⟩ :=
    (shr_r64_imm8_effect_step 0x11367f 0x49 0xee 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f15.machine f15.bindingsSupported)
      (programText_slice (programLoaded_codeIn f15.loaded) 0x1367f _ (by decide) (by decide +kernel))
      e15.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13683 (by decide)))
  change (shrR64Effect 0x11367f 4 14 63 u15).Holds u15 u16 at e16
  have f16 := f15.after_registers ready16 e16.agrees (by simp [shrR64Effect_components, Component.Covers]) (by simp [shrR64Effect_components])
  have g16r14 : ((Operand.reg 14 : Operand 64).read u16) = (((((~~~t.regValue .rcx) ||| slot s t 48) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48))) ||| (slot s t 48 &&& (~~~t.regValue .rcx))) >>> 63) := by
    have h := e16.writes
    change ((Operand.reg 14 : Operand 64).read u16) = ((Operand.reg 14 : Operand 64).read u15) >>> 63 at h
    rw [g15r14] at h
    exact h
  obtain ⟨u17, run17, ready17, e17⟩ :=
    (mov_m64_r64_effect_step_any 0x113683 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f16.machine f16.bindingsSupported)
      (programText_slice (programLoaded_codeIn f16.loaded) 0x13683 _ (by decide) (by decide +kernel))
      ⟨e16.rip, ScalarFrame.stack_writable pre.toCalleePre f16 (offset := 8) (len := 8) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f16 (offset := 8) (len := 8) (codeOffset := 0x13683) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13688 (by decide)))
  change (movM64R64Effect 0x113683 14 (.sib 4 none 0 (.d8 8)) u16).Holds u16 u17 at e17
  have ag17 : AgreesExcept [.mem (stackPtr u16 + 8) 8, .rip] u16 u17 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e17.agrees
  have f17 := FirstRound.after_store pre f16 ready17 (offset := 8) (by decide) ag17
  have wr17 : slot s u17 8 = (((((~~~t.regValue .rcx) ||| slot s t 48) &&& ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48))) ||| (slot s t 48 &&& (~~~t.regValue .rcx))) >>> 63) := by
    have h := e17.writes
    change memLoad u17.external (stackPtr u16 + 8) 64 = ((Operand.reg 14 : Operand 64).read u16) at h
    rw [f16.rsp, g16r14] at h
    exact h
  have g14r9 : ((Operand.reg 9 : Operand 64).read u14) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48)) :=
    (e14.agrees.read (by simp [andR64R64Effect_components])).trans g13r9
  have g15r9 : ((Operand.reg 9 : Operand 64).read u15) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48)) :=
    (e15.agrees.read (by simp [orR64R64Effect_components])).trans g14r9
  have g16r9 : ((Operand.reg 9 : Operand 64).read u16) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48)) :=
    (e16.agrees.read (by simp [shrR64Effect_components])).trans g15r9
  have g17r9 : ((Operand.reg 9 : Operand 64).read u17) = ((((0 : BitVec 64) - (slot s t 8))).sshiftRight 63 + (t.regValue .rcx - slot s t 48)) :=
    (e17.agrees.read (by simp [movM64R64Effect_components])).trans g16r9
  have ag : AgreesExcept (changes s [10, 9, 14, 13, 15]) t u17 := ((((((((((((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).trans ag17).mono (by simp only [leaR64Effect_components, xorR32R32Effect_components, subR64M64Effect_components, movR64R64Effect_components, movR64M64Effect_components, subR64R64Effect_components, sarR64Effect_components, addR64R64Effect_components, notR64Effect_components, andR64R64Effect_components, orR64R64Effect_components, shrR64Effect_components, f16.rsp]; simp [changes])
  refine ⟨u17, ⟨17, ((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17)⟩, f17, e17.rip, ag, ?_, ?_⟩
  · change ((Operand.reg 9 : Operand 64).read u17) = _
    exact g17r9
  · exact wr17

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow
