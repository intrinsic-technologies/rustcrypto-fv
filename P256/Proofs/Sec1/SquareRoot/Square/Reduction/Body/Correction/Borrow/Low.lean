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
theorem low [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s t 32 112 112)
    (rip : t.RIP = 0x113627) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      ScalarFrame.FrameState s u 32 112 112 ∧ u.RIP = 0x11364b ∧
      AgreesExcept (changes s [6, 9, 14]) t u ∧
      u.regValue .rsi = (t.regValue .rbx - t.regValue .r11) ∧
      slot s u 8 = borrow (t.regValue .rbx) (t.regValue .r11) (t.regValue .rbx - t.regValue .r11) := by
  have f0 := frame
  have g0r3 : ((Operand.reg 3 : Operand 64).read t) = t.regValue .rbx := rfl
  have g0r11 : ((Operand.reg 11 : Operand 64).read t) = t.regValue .r11 := rfl
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_r64_r64_effect_step 0x113627 0x48 0xde (by simp [RexWPrefix]) (by decide)).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x13627 _ (by decide) (by decide +kernel))
      rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1362a (by decide)))
  change (movR64R64Effect 0x113627 6 3 t).Holds t u1 at e1
  have f1 := f0.after_registers ready1 e1.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g1r6 : ((Operand.reg 6 : Operand 64).read u1) = t.regValue .rbx := by
    have h := e1.writes
    change ((Operand.reg 6 : Operand 64).read u1) = ((Operand.reg 3 : Operand 64).read t) at h
    rw [g0r3] at h
    exact h
  have g1r11 : ((Operand.reg 11 : Operand 64).read u1) = t.regValue .r11 :=
    (e1.agrees.read (by simp [movR64R64Effect_components])).trans g0r11
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (sub_r64_r64_effect_step 0x11362a 0x4c 0xde (by simp [RexWPrefix]) (by decide)).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x1362a _ (by decide) (by decide +kernel))
      e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1362d (by decide)))
  change (subR64R64Effect 0x11362a 6 11 u1).Holds u1 u2 at e2
  have f2 := f1.after_registers ready2 e2.agrees (by simp [subR64R64Effect_components, Component.Covers]) (by simp [subR64R64Effect_components])
  have g2r6 : ((Operand.reg 6 : Operand 64).read u2) = (t.regValue .rbx - t.regValue .r11) := by
    have h := e2.writes
    change ((Operand.reg 6 : Operand 64).read u2) = ((Operand.reg 6 : Operand 64).read u1) - ((Operand.reg 11 : Operand 64).read u1) at h
    rw [g1r11, g1r6] at h
    exact h
  have g1r3 : ((Operand.reg 3 : Operand 64).read u1) = t.regValue .rbx :=
    (e1.agrees.read (by simp [movR64R64Effect_components])).trans g0r3
  have g2r3 : ((Operand.reg 3 : Operand 64).read u2) = t.regValue .rbx :=
    (e2.agrees.read (by simp [subR64R64Effect_components])).trans g1r3
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (mov_r64_r64_effect_step 0x11362d 0x49 0xd9 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x1362d _ (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13630 (by decide)))
  change (movR64R64Effect 0x11362d 9 3 u2).Holds u2 u3 at e3
  have f3 := f2.after_registers ready3 e3.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g3r9 : ((Operand.reg 9 : Operand 64).read u3) = t.regValue .rbx := by
    have h := e3.writes
    change ((Operand.reg 9 : Operand 64).read u3) = ((Operand.reg 3 : Operand 64).read u2) at h
    rw [g2r3] at h
    exact h
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (not_r64_effect_step 0x113630 0x49 0xd1 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x13630 _ (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13633 (by decide)))
  change (notR64Effect 0x113630 9 u3).Holds u3 u4 at e4
  have f4 := f3.after_registers ready4 e4.agrees (by simp [notR64Effect_components, Component.Covers]) (by simp [notR64Effect_components])
  have g4r9 : ((Operand.reg 9 : Operand 64).read u4) = (~~~t.regValue .rbx) := by
    have h := e4.writes
    change ((Operand.reg 9 : Operand 64).read u4) = ~~~((Operand.reg 9 : Operand 64).read u3) at h
    rw [g3r9] at h
    exact h
  have g2r11 : ((Operand.reg 11 : Operand 64).read u2) = t.regValue .r11 :=
    (e2.agrees.read (by simp [subR64R64Effect_components])).trans g1r11
  have g3r11 : ((Operand.reg 11 : Operand 64).read u3) = t.regValue .r11 :=
    (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r11
  have g4r11 : ((Operand.reg 11 : Operand 64).read u4) = t.regValue .r11 :=
    (e4.agrees.read (by simp [notR64Effect_components])).trans g3r11
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (mov_r64_r64_effect_step 0x113633 0x4d 0xde (by simp [RexWPrefix]) (by decide)).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x13633 _ (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13636 (by decide)))
  change (movR64R64Effect 0x113633 14 11 u4).Holds u4 u5 at e5
  have f5 := f4.after_registers ready5 e5.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have g5r14 : ((Operand.reg 14 : Operand 64).read u5) = t.regValue .r11 := by
    have h := e5.writes
    change ((Operand.reg 14 : Operand 64).read u5) = ((Operand.reg 11 : Operand 64).read u4) at h
    rw [g4r11] at h
    exact h
  have g5r9 : ((Operand.reg 9 : Operand 64).read u5) = (~~~t.regValue .rbx) :=
    (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r9
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (and_r64_r64_effect_step 0x113636 0x4d 0xce (by simp [RexWPrefix]) (by decide)).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x13636 _ (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13639 (by decide)))
  change (andR64R64Effect 0x113636 14 9 u5).Holds u5 u6 at e6
  have f6 := f5.after_registers ready6 e6.agrees (by simp [andR64R64Effect_components, Component.Covers]) (by simp [andR64R64Effect_components])
  have g6r14 : ((Operand.reg 14 : Operand 64).read u6) = (t.regValue .r11 &&& (~~~t.regValue .rbx)) := by
    have h := e6.writes
    change ((Operand.reg 14 : Operand 64).read u6) = ((Operand.reg 14 : Operand 64).read u5) &&& ((Operand.reg 9 : Operand 64).read u5) at h
    rw [g5r9, g5r14] at h
    exact h
  have g5r11 : ((Operand.reg 11 : Operand 64).read u5) = t.regValue .r11 :=
    (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r11
  have g6r11 : ((Operand.reg 11 : Operand 64).read u6) = t.regValue .r11 :=
    (e6.agrees.read (by simp [andR64R64Effect_components])).trans g5r11
  have g6r9 : ((Operand.reg 9 : Operand 64).read u6) = (~~~t.regValue .rbx) :=
    (e6.agrees.read (by simp [andR64R64Effect_components])).trans g5r9
  obtain ⟨u7, run7, ready7, e7⟩ :=
    (or_r64_r64_effect_step 0x113639 0x4d 0xd9 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x13639 _ (by decide) (by decide +kernel))
      e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1363c (by decide)))
  change (orR64R64Effect 0x113639 9 11 u6).Holds u6 u7 at e7
  have f7 := f6.after_registers ready7 e7.agrees (by simp [orR64R64Effect_components, Component.Covers]) (by simp [orR64R64Effect_components])
  have g7r9 : ((Operand.reg 9 : Operand 64).read u7) = ((~~~t.regValue .rbx) ||| t.regValue .r11) := by
    have h := e7.writes
    change ((Operand.reg 9 : Operand 64).read u7) = ((Operand.reg 9 : Operand 64).read u6) ||| ((Operand.reg 11 : Operand 64).read u6) at h
    rw [g6r11, g6r9] at h
    exact h
  have g3r6 : ((Operand.reg 6 : Operand 64).read u3) = (t.regValue .rbx - t.regValue .r11) :=
    (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r6
  have g4r6 : ((Operand.reg 6 : Operand 64).read u4) = (t.regValue .rbx - t.regValue .r11) :=
    (e4.agrees.read (by simp [notR64Effect_components])).trans g3r6
  have g5r6 : ((Operand.reg 6 : Operand 64).read u5) = (t.regValue .rbx - t.regValue .r11) :=
    (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r6
  have g6r6 : ((Operand.reg 6 : Operand 64).read u6) = (t.regValue .rbx - t.regValue .r11) :=
    (e6.agrees.read (by simp [andR64R64Effect_components])).trans g5r6
  have g7r6 : ((Operand.reg 6 : Operand 64).read u7) = (t.regValue .rbx - t.regValue .r11) :=
    (e7.agrees.read (by simp [orR64R64Effect_components])).trans g6r6
  obtain ⟨u8, run8, ready8, e8⟩ :=
    (and_r64_r64_effect_step 0x11363c 0x49 0xf1 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x1363c _ (by decide) (by decide +kernel))
      e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1363f (by decide)))
  change (andR64R64Effect 0x11363c 9 6 u7).Holds u7 u8 at e8
  have f8 := f7.after_registers ready8 e8.agrees (by simp [andR64R64Effect_components, Component.Covers]) (by simp [andR64R64Effect_components])
  have g8r9 : ((Operand.reg 9 : Operand 64).read u8) = (((~~~t.regValue .rbx) ||| t.regValue .r11) &&& (t.regValue .rbx - t.regValue .r11)) := by
    have h := e8.writes
    change ((Operand.reg 9 : Operand 64).read u8) = ((Operand.reg 9 : Operand 64).read u7) &&& ((Operand.reg 6 : Operand 64).read u7) at h
    rw [g7r6, g7r9] at h
    exact h
  have g7r14 : ((Operand.reg 14 : Operand 64).read u7) = (t.regValue .r11 &&& (~~~t.regValue .rbx)) :=
    (e7.agrees.read (by simp [orR64R64Effect_components])).trans g6r14
  have g8r14 : ((Operand.reg 14 : Operand 64).read u8) = (t.regValue .r11 &&& (~~~t.regValue .rbx)) :=
    (e8.agrees.read (by simp [andR64R64Effect_components])).trans g7r14
  obtain ⟨u9, run9, ready9, e9⟩ :=
    (or_r64_r64_effect_step 0x11363f 0x4d 0xf1 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x1363f _ (by decide) (by decide +kernel))
      e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13642 (by decide)))
  change (orR64R64Effect 0x11363f 9 14 u8).Holds u8 u9 at e9
  have f9 := f8.after_registers ready9 e9.agrees (by simp [orR64R64Effect_components, Component.Covers]) (by simp [orR64R64Effect_components])
  have g9r9 : ((Operand.reg 9 : Operand 64).read u9) = ((((~~~t.regValue .rbx) ||| t.regValue .r11) &&& (t.regValue .rbx - t.regValue .r11)) ||| (t.regValue .r11 &&& (~~~t.regValue .rbx))) := by
    have h := e9.writes
    change ((Operand.reg 9 : Operand 64).read u9) = ((Operand.reg 9 : Operand 64).read u8) ||| ((Operand.reg 14 : Operand 64).read u8) at h
    rw [g8r14, g8r9] at h
    exact h
  obtain ⟨u10, run10, ready10, e10⟩ :=
    (shr_r64_imm8_effect_step 0x113642 0x49 0xe9 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x13642 _ (by decide) (by decide +kernel))
      e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13646 (by decide)))
  change (shrR64Effect 0x113642 4 9 63 u9).Holds u9 u10 at e10
  have f10 := f9.after_registers ready10 e10.agrees (by simp [shrR64Effect_components, Component.Covers]) (by simp [shrR64Effect_components])
  have g10r9 : ((Operand.reg 9 : Operand 64).read u10) = (((((~~~t.regValue .rbx) ||| t.regValue .r11) &&& (t.regValue .rbx - t.regValue .r11)) ||| (t.regValue .r11 &&& (~~~t.regValue .rbx))) >>> 63) := by
    have h := e10.writes
    change ((Operand.reg 9 : Operand 64).read u10) = ((Operand.reg 9 : Operand 64).read u9) >>> 63 at h
    rw [g9r9] at h
    exact h
  obtain ⟨u11, run11, ready11, e11⟩ :=
    (mov_m64_r64_effect_step_any 0x113646 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x13646 _ (by decide) (by decide +kernel))
      ⟨e10.rip, ScalarFrame.stack_writable pre.toCalleePre f10 (offset := 8) (len := 8) (by decide) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f10 (offset := 8) (len := 8) (codeOffset := 0x13646) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1364b (by decide)))
  change (movM64R64Effect 0x113646 9 (.sib 4 none 0 (.d8 8)) u10).Holds u10 u11 at e11
  have ag11 : AgreesExcept [.mem (stackPtr u10 + 8) 8, .rip] u10 u11 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e11.agrees
  have f11 := FirstRound.after_store pre f10 ready11 (offset := 8) (by decide) ag11
  have wr11 : slot s u11 8 = (((((~~~t.regValue .rbx) ||| t.regValue .r11) &&& (t.regValue .rbx - t.regValue .r11)) ||| (t.regValue .r11 &&& (~~~t.regValue .rbx))) >>> 63) := by
    have h := e11.writes
    change memLoad u11.external (stackPtr u10 + 8) 64 = ((Operand.reg 9 : Operand 64).read u10) at h
    rw [f10.rsp, g10r9] at h
    exact h
  have g8r6 : ((Operand.reg 6 : Operand 64).read u8) = (t.regValue .rbx - t.regValue .r11) :=
    (e8.agrees.read (by simp [andR64R64Effect_components])).trans g7r6
  have g9r6 : ((Operand.reg 6 : Operand 64).read u9) = (t.regValue .rbx - t.regValue .r11) :=
    (e9.agrees.read (by simp [orR64R64Effect_components])).trans g8r6
  have g10r6 : ((Operand.reg 6 : Operand 64).read u10) = (t.regValue .rbx - t.regValue .r11) :=
    (e10.agrees.read (by simp [shrR64Effect_components])).trans g9r6
  have g11r6 : ((Operand.reg 6 : Operand 64).read u11) = (t.regValue .rbx - t.regValue .r11) :=
    (e11.agrees.read (by simp [movM64R64Effect_components])).trans g10r6
  have ag : AgreesExcept (changes s [6, 9, 14]) t u11 := ((((((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans ag11).mono (by simp only [movR64R64Effect_components, subR64R64Effect_components, notR64Effect_components, andR64R64Effect_components, orR64R64Effect_components, shrR64Effect_components, f10.rsp]; simp [changes])
  refine ⟨u11, ⟨11, ((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11)⟩, f11, e11.rip, ag, ?_, ?_⟩
  · change ((Operand.reg 6 : Operand 64).read u11) = _
    exact g11r6
  · exact wr11

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow
