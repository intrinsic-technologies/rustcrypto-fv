import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.ThirdLow

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper

open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Field.Montgomery (add64 adc64 product64)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem third_machine_middle [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : Second s t v) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ ThirdMachineMiddle s t u := by
  let a := t.regValue .r13
  let b := t.regValue .rbp
  let c := t.regValue .rbx
  let d := t.regValue .r14
  let extra := t.regValue .r9
  generalize eq_p0 : product64 a 0xffffffffffffffff = p0
  generalize eq_p1 : product64 a 0xffffffff = p1
  generalize eq_x : add64 p1.1 b = x
  generalize eq_h : adc64 p1.2 0 x.2 = h
  generalize eq_z : add64 p0.1 a = z
  generalize eq_y : adc64 x.1 p0.2 z.2 = y
  generalize eq_k : adc64 h.1 0 y.2 = k
  generalize eq_middle : add64 k.1 c = middle
  generalize eq_upper : add64 d extra = upper
  generalize eq_p3 : product64 0xffffffff00000001 a = p3

  have lowWords : thirdLow a b = (y.1, k.1) := by
    as_aux_lemma =>
      simp only [thirdLow, eq_p0, eq_p1, eq_x, eq_h, eq_z, eq_y, eq_k]
  obtain ⟨u18, ⟨fuelLow, runLow⟩, low⟩ := third_machine_low pre state
  have f18 : ScalarFrame.FrameState s u18 32 112 112 := by
    as_aux_lemma =>
      exact low.frame
  have m18 := low.memory
  have g18r12 : ((Operand.reg 12 : Operand 64).read u18) = y.1 := by
    as_aux_lemma =>
      have h := low.r12; change ((Operand.reg 12 : Operand 64).read u18) = (thirdLow a b).1 at h; rw [lowWords] at h; exact h
  have g18r15 : ((Operand.reg 15 : Operand 64).read u18) = k.1 := by
    as_aux_lemma =>
      have h := low.r15; change ((Operand.reg 15 : Operand 64).read u18) = (thirdLow a b).2 at h; rw [lowWords] at h; exact h
  have g18r11 : ((Operand.reg 11 : Operand 64).read u18) = a := low.r11
  have g18r0 : ((Operand.reg 0 : Operand 64).read u18) = 0 := low.rax
  have g18r2 : ((Operand.reg 2 : Operand 64).read u18) = 0 := low.rdx
  have g18r3 : ((Operand.reg 3 : Operand 64).read u18) = c := low.rbx
  have g18r14 : ((Operand.reg 14 : Operand 64).read u18) = d := low.r14
  have g18r9 : ((Operand.reg 9 : Operand 64).read u18) = extra := low.r9
  have g18r7 : ((Operand.reg 7 : Operand 64).read u18) = s.regValue .rdi := low.rdi
  have g18r6 : ((Operand.reg 6 : Operand 64).read u18) = 0xffffffff := low.rsi
  obtain ⟨u19, run19, ready19, e19⟩ :=
    (xor_r32_r32_rex_effect_step 0x11354d 0x45 0xed (by simp [RexNoWPrefix]) (by decide)).advances (readyToStep f18.machine f18.bindingsSupported)
      (programText_slice (programLoaded_codeIn f18.loaded) 0x1354d _ (by decide) (by decide +kernel))
      low.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13550 (by decide)))
  change (xorR32R32Effect 0x11354d 3 13 13 u18).Holds u18 u19 at e19
  have f19 : ScalarFrame.FrameState s u19 32 112 112 := by
    as_aux_lemma =>
      exact f18.after_registers ready19 e19.agrees (by simp [xorR32R32Effect_components, Component.Covers]) (by simp [xorR32R32Effect_components])
  have m19 : u19.external = t.external := (e19.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])).trans m18
  have g19r13 : ((Operand.reg 13 : Operand 64).read u19) = 0 := by
    as_aux_lemma =>
      simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, Write.AllHold] using e19.writes
  have g19r3 : ((Operand.reg 3 : Operand 64).read u19) = c := (e19.agrees.read (by simp [xorR32R32Effect_components])).trans g18r3
  have g19r15 : ((Operand.reg 15 : Operand 64).read u19) = k.1 := (e19.agrees.read (by simp [xorR32R32Effect_components])).trans g18r15
  obtain ⟨u20, run20, ready20, e20⟩ :=
    (add_r64_r64_effect_step 0x113550 0x49 0xdf (by simp [RexWPrefix]) (by decide)).advances (readyToStep f19.machine f19.bindingsSupported)
      (programText_slice (programLoaded_codeIn f19.loaded) 0x13550 _ (by decide) (by decide +kernel))
      e19.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13553 (by decide)))
  change (addR64R64Effect 0x113550 15 3 u19).Holds u19 u20 at e20
  have f20 : ScalarFrame.FrameState s u20 32 112 112 := by
    as_aux_lemma =>
      exact f19.after_registers ready20 e20.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have m20 : u20.external = t.external := (e20.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans m19
  have g20r15 : ((Operand.reg 15 : Operand 64).read u20) = middle.1 := by
    as_aux_lemma =>
      have h := e20.writes
      change ((Operand.reg 15 : Operand 64).read u20) = (addSpec ((Operand.reg 15 : Operand 64).read u19) ((Operand.reg 3 : Operand 64).read u19)).1 at h
      rw [g19r3, g19r15] at h
      simpa only [← eq_middle, add64] using h
  have cf20 : (StatusFlags.ofRFLAGS u20.RFLAGS).CF = middle.2 := by
    as_aux_lemma =>
      have h := e20.flags.1
      change (StatusFlags.ofRFLAGS u20.RFLAGS).CF = (addSpec ((Operand.reg 15 : Operand 64).read u19) ((Operand.reg 3 : Operand 64).read u19)).2.CF at h
      rw [g19r3, g19r15] at h
      simpa only [← eq_middle, add64] using h
  have g20r13 : ((Operand.reg 13 : Operand 64).read u20) = 0 := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r13
  obtain ⟨u21, run21, ready21, e21⟩ :=
    (setcc_r8_rex_effect_step 0x113553 0x41 0x92 0xc5 (by simp [RexPrefix]) (.inl rfl) (by decide)).advances (readyToStep f20.machine f20.bindingsSupported)
      (programText_slice (programLoaded_codeIn f20.loaded) 0x13553 _ (by decide) (by decide +kernel))
      e20.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13557 (by decide)))
  change (setccR8Effect 0x113553 4 13 2 u20).Holds u20 u21 at e21
  have f21 : ScalarFrame.FrameState s u21 32 112 112 := by
    as_aux_lemma =>
      exact f20.after_registers ready21 e21.agrees (by simp [setccR8Effect_components, Component.Covers]) (by simp [setccR8Effect_components])
  have m21 : u21.external = t.external := (e21.agrees.external (by simp [setccR8Effect_components, Component.Covers])).trans m20
  have g21r13 : ((Operand.reg 13 : Operand 64).read u21) = (BitVec.ofNat 64 middle.2.toNat) := by
    as_aux_lemma =>
      have h := e21.writes
      change ((Operand.reg 13 : Operand 64).read u21) = mergeGPR 8 (if (StatusFlags.ofRFLAGS u20.RFLAGS).CF then 1 else 0) ((Operand.reg 13 : Operand 64).read u20) at h
      rw [g20r13, cf20] at h
      simpa only [BitVec.ofNat_eq_ofNat, P256.Proofs.Field.Subtract.setb_zero_value] using h
  have g19r0 : ((Operand.reg 0 : Operand 64).read u19) = 0 := (e19.agrees.read (by simp [xorR32R32Effect_components])).trans g18r0
  have g20r0 : ((Operand.reg 0 : Operand 64).read u20) = 0 := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r0
  have g21r0 : ((Operand.reg 0 : Operand 64).read u21) = 0 := (e21.agrees.read (by simp [setccR8Effect_components])).trans g20r0
  have g21r15 : ((Operand.reg 15 : Operand 64).read u21) = middle.1 := (e21.agrees.read (by simp [setccR8Effect_components])).trans g20r15
  obtain ⟨u22, run22, ready22, e22⟩ :=
    (add_r64_r64_effect_step 0x113557 0x49 0xc7 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f21.machine f21.bindingsSupported)
      (programText_slice (programLoaded_codeIn f21.loaded) 0x13557 _ (by decide) (by decide +kernel))
      e21.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1355a (by decide)))
  change (addR64R64Effect 0x113557 15 0 u21).Holds u21 u22 at e22
  have f22 : ScalarFrame.FrameState s u22 32 112 112 := by
    as_aux_lemma =>
      exact f21.after_registers ready22 e22.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have m22 : u22.external = t.external := (e22.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans m21
  have g22r15 : ((Operand.reg 15 : Operand 64).read u22) = middle.1 := by
    as_aux_lemma =>
      have h := e22.writes
      change ((Operand.reg 15 : Operand 64).read u22) = (addSpec ((Operand.reg 15 : Operand 64).read u21) ((Operand.reg 0 : Operand 64).read u21)).1 at h
      rw [g21r0, g21r15] at h
      simpa only [addSpec, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  have cf22 : (StatusFlags.ofRFLAGS u22.RFLAGS).CF = false := by
    as_aux_lemma =>
      have h := e22.flags.1
      change (StatusFlags.ofRFLAGS u22.RFLAGS).CF = (addSpec ((Operand.reg 15 : Operand 64).read u21) ((Operand.reg 0 : Operand 64).read u21)).2.CF at h
      rw [g21r0, g21r15] at h
      simpa only [addSpec, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_zero, Nat.add_zero, ne_eq, not_true_eq_false, decide_false] using h
  have g19r9 : ((Operand.reg 9 : Operand 64).read u19) = extra := (e19.agrees.read (by simp [xorR32R32Effect_components])).trans g18r9
  have g20r9 : ((Operand.reg 9 : Operand 64).read u20) = extra := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r9
  have g21r9 : ((Operand.reg 9 : Operand 64).read u21) = extra := (e21.agrees.read (by simp [setccR8Effect_components])).trans g20r9
  have g22r9 : ((Operand.reg 9 : Operand 64).read u22) = extra := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r9
  have g19r14 : ((Operand.reg 14 : Operand 64).read u19) = d := (e19.agrees.read (by simp [xorR32R32Effect_components])).trans g18r14
  have g20r14 : ((Operand.reg 14 : Operand 64).read u20) = d := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r14
  have g21r14 : ((Operand.reg 14 : Operand 64).read u21) = d := (e21.agrees.read (by simp [setccR8Effect_components])).trans g20r14
  have g22r14 : ((Operand.reg 14 : Operand 64).read u22) = d := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r14
  obtain ⟨u23, run23, ready23, e23⟩ :=
    (lea_r64_effect_step 0x11355a 0x4b (by simp [RexWPrefix]) 1 (.sib 9 (some 14) 0 .none) (by decide) rfl rfl).advances (readyToStep f22.machine f22.bindingsSupported)
      (programText_slice (programLoaded_codeIn f22.loaded) 0x1355a _ (by decide) (by decide +kernel))
      e22.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1355e (by decide)))
  change (leaR64Effect 0x11355a 1 (.sib 9 (some 14) 0 .none) u22).Holds u22 u23 at e23
  have f23 : ScalarFrame.FrameState s u23 32 112 112 := by
    as_aux_lemma =>
      exact f22.after_registers ready23 e23.agrees (by simp [leaR64Effect_components, Component.Covers]) (by simp [leaR64Effect_components])
  have m23 : u23.external = t.external := (e23.agrees.external (by simp [leaR64Effect_components, Component.Covers])).trans m22
  have g23r1 : ((Operand.reg 1 : Operand 64).read u23) = upper.1 := by
    as_aux_lemma =>
      have h := e23.writes
      change ((Operand.reg 1 : Operand 64).read u23) = ((Operand.reg 9 : Operand 64).read u22) + (((Operand.reg 14 : Operand 64).read u22) <<< 0) + 0 at h
      rw [g22r9, g22r14] at h
      simpa only [← eq_upper, add64, addSpec, BitVec.shiftLeft_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add, BitVec.add_comm] using h
  have g19r2 : ((Operand.reg 2 : Operand 64).read u19) = 0 := (e19.agrees.read (by simp [xorR32R32Effect_components])).trans g18r2
  have g20r2 : ((Operand.reg 2 : Operand 64).read u20) = 0 := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r2
  have g21r2 : ((Operand.reg 2 : Operand 64).read u21) = 0 := (e21.agrees.read (by simp [setccR8Effect_components])).trans g20r2
  have g22r2 : ((Operand.reg 2 : Operand 64).read u22) = 0 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r2
  have g23r2 : ((Operand.reg 2 : Operand 64).read u23) = 0 := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r2
  have g22r13 : ((Operand.reg 13 : Operand 64).read u22) = (BitVec.ofNat 64 middle.2.toNat) := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r13
  have g23r13 : ((Operand.reg 13 : Operand 64).read u23) = (BitVec.ofNat 64 middle.2.toNat) := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r13
  have cf23 : (StatusFlags.ofRFLAGS u23.RFLAGS).CF = false := by
    as_aux_lemma =>
      rw [e23.agrees.statusFlags (by simp [leaR64Effect_components]), cf22]
  obtain ⟨u24, run24, ready24, e24⟩ :=
    (adc_r64_r64_effect_step 0x11355e 0x49 0xd5 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f23.machine f23.bindingsSupported)
      (programText_slice (programLoaded_codeIn f23.loaded) 0x1355e _ (by decide) (by decide +kernel))
      e23.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13561 (by decide)))
  change (adcR64R64Effect 0x11355e 13 2 u23).Holds u23 u24 at e24
  have f24 : ScalarFrame.FrameState s u24 32 112 112 := by
    as_aux_lemma =>
      exact f23.after_registers ready24 e24.agrees (by simp [adcR64R64Effect_components, Component.Covers]) (by simp [adcR64R64Effect_components])
  have m24 : u24.external = t.external := (e24.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans m23
  have g24r13 : ((Operand.reg 13 : Operand 64).read u24) = (BitVec.ofNat 64 middle.2.toNat) := by
    as_aux_lemma =>
      have h := e24.writes
      change ((Operand.reg 13 : Operand 64).read u24) = (adcSpec ((Operand.reg 13 : Operand 64).read u23) ((Operand.reg 2 : Operand 64).read u23) (u23.RFLAGS.extractLsb' 0 1)).1 at h
      rw [g23r2, g23r13, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf23] at h
      simpa only [adc_zero_false_word] using h
  obtain ⟨u25, run25, ready25, e25⟩ :=
    (mov_r64_m64_effect_step 0x113561 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl).advances (readyToStep f24.machine f24.bindingsSupported)
      (programText_slice (programLoaded_codeIn f24.loaded) 0x13561 _ (by decide) (by decide +kernel))
      ⟨e24.rip, ScalarFrame.stack_readable pre.toCalleePre f24 (offset := 32) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13566 (by decide)))
  change (movR64M64Effect 0x113561 5 (.sib 4 none 0 (.d8 32)) u24).Holds u24 u25 at e25
  have f25 : ScalarFrame.FrameState s u25 32 112 112 := by
    as_aux_lemma =>
      exact f24.after_registers ready25 e25.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have m25 : u25.external = t.external := (e25.agrees.external (by simp [movR64M64Effect_components, Component.Covers])).trans m24
  have load25 : memLoad u24.external (stackPtr u24 + 32) 64 = 0xffffffff00000001 := by
    as_aux_lemma =>
      rw [f24.rsp, m24]
      exact state.slots.p3
  have g25r5 : ((Operand.reg 5 : Operand 64).read u25) = 0xffffffff00000001 := by
    as_aux_lemma =>
      have h := e25.writes
      change ((Operand.reg 5 : Operand 64).read u25) = memLoad u24.external (stackPtr u24 + 32) 64 at h
      rw [load25] at h
      exact h
  obtain ⟨u26, run26, ready26, e26⟩ :=
    (mov_r64_r64_effect_step 0x113566 0x48 0xe8 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f25.machine f25.bindingsSupported)
      (programText_slice (programLoaded_codeIn f25.loaded) 0x13566 _ (by decide) (by decide +kernel))
      e25.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13569 (by decide)))
  change (movR64R64Effect 0x113566 0 5 u25).Holds u25 u26 at e26
  have f26 : ScalarFrame.FrameState s u26 32 112 112 := by
    as_aux_lemma =>
      exact f25.after_registers ready26 e26.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have m26 : u26.external = t.external := (e26.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans m25
  have g26r0 : ((Operand.reg 0 : Operand 64).read u26) = 0xffffffff00000001 := by
    as_aux_lemma =>
      have h := e26.writes
      change ((Operand.reg 0 : Operand 64).read u26) = ((Operand.reg 5 : Operand 64).read u25) at h
      rw [g25r5] at h
      exact h
  have g19r11 : ((Operand.reg 11 : Operand 64).read u19) = a := (e19.agrees.read (by simp [xorR32R32Effect_components])).trans g18r11
  have g20r11 : ((Operand.reg 11 : Operand 64).read u20) = a := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r11
  have g21r11 : ((Operand.reg 11 : Operand 64).read u21) = a := (e21.agrees.read (by simp [setccR8Effect_components])).trans g20r11
  have g22r11 : ((Operand.reg 11 : Operand 64).read u22) = a := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r11
  have g23r11 : ((Operand.reg 11 : Operand 64).read u23) = a := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r11
  have g24r11 : ((Operand.reg 11 : Operand 64).read u24) = a := (e24.agrees.read (by simp [adcR64R64Effect_components])).trans g23r11
  have g25r11 : ((Operand.reg 11 : Operand 64).read u25) = a := (e25.agrees.read (by simp [movR64M64Effect_components])).trans g24r11
  have g26r11 : ((Operand.reg 11 : Operand 64).read u26) = a := (e26.agrees.read (by simp [movR64R64Effect_components])).trans g25r11
  obtain ⟨u27, run27, ready27, e27⟩ :=
    (mul_r64_effect_step 0x113569 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f26.machine f26.bindingsSupported)
      (programText_slice (programLoaded_codeIn f26.loaded) 0x13569 _ (by decide) (by decide +kernel))
      e26.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1356c (by decide)))
  change (mulR64Effect 0x113569 11 u26).Holds u26 u27 at e27
  have f27 : ScalarFrame.FrameState s u27 32 112 112 := by
    as_aux_lemma =>
      exact f26.after_registers ready27 e27.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have m27 : u27.external = t.external := (e27.agrees.external (by simp [mulR64Effect_components, Component.Covers])).trans m26
  have g27r0 : ((Operand.reg 0 : Operand 64).read u27) = p3.1 := by
    as_aux_lemma =>
      have h := e27.writes.1
      change ((Operand.reg 0 : Operand 64).read u27) = ((Operand.reg 0 : Operand 64).read u26) * ((Operand.reg 11 : Operand 64).read u26) at h
      rw [g26r0, g26r11] at h
      simpa only [← eq_p3, product64] using h
  have g27r2 : ((Operand.reg 2 : Operand 64).read u27) = p3.2 := by
    as_aux_lemma =>
      have h := e27.writes.2
      change ((Operand.reg 2 : Operand 64).read u27) = mulHigh64 ((Operand.reg 0 : Operand 64).read u26) ((Operand.reg 11 : Operand 64).read u26) at h
      rw [g26r0, g26r11] at h
      simpa only [← eq_p3, product64] using h
  have g19r12 : ((Operand.reg 12 : Operand 64).read u19) = y.1 := (e19.agrees.read (by simp [xorR32R32Effect_components])).trans g18r12
  have g20r12 : ((Operand.reg 12 : Operand 64).read u20) = y.1 := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r12
  have g21r12 : ((Operand.reg 12 : Operand 64).read u21) = y.1 := (e21.agrees.read (by simp [setccR8Effect_components])).trans g20r12
  have g22r12 : ((Operand.reg 12 : Operand 64).read u22) = y.1 := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r12
  have g23r12 : ((Operand.reg 12 : Operand 64).read u23) = y.1 := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r12
  have g24r12 : ((Operand.reg 12 : Operand 64).read u24) = y.1 := (e24.agrees.read (by simp [adcR64R64Effect_components])).trans g23r12
  have g25r12 : ((Operand.reg 12 : Operand 64).read u25) = y.1 := (e25.agrees.read (by simp [movR64M64Effect_components])).trans g24r12
  have g26r12 : ((Operand.reg 12 : Operand 64).read u26) = y.1 := (e26.agrees.read (by simp [movR64R64Effect_components])).trans g25r12
  have g27r12 : ((Operand.reg 12 : Operand 64).read u27) = y.1 := (e27.agrees.read (by simp [mulR64Effect_components])).trans g26r12
  have g23r15 : ((Operand.reg 15 : Operand 64).read u23) = middle.1 := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r15
  have g24r15 : ((Operand.reg 15 : Operand 64).read u24) = middle.1 := (e24.agrees.read (by simp [adcR64R64Effect_components])).trans g23r15
  have g25r15 : ((Operand.reg 15 : Operand 64).read u25) = middle.1 := (e25.agrees.read (by simp [movR64M64Effect_components])).trans g24r15
  have g26r15 : ((Operand.reg 15 : Operand 64).read u26) = middle.1 := (e26.agrees.read (by simp [movR64R64Effect_components])).trans g25r15
  have g27r15 : ((Operand.reg 15 : Operand 64).read u27) = middle.1 := (e27.agrees.read (by simp [mulR64Effect_components])).trans g26r15
  have g25r13 : ((Operand.reg 13 : Operand 64).read u25) = (BitVec.ofNat 64 middle.2.toNat) := (e25.agrees.read (by simp [movR64M64Effect_components])).trans g24r13
  have g26r13 : ((Operand.reg 13 : Operand 64).read u26) = (BitVec.ofNat 64 middle.2.toNat) := (e26.agrees.read (by simp [movR64R64Effect_components])).trans g25r13
  have g27r13 : ((Operand.reg 13 : Operand 64).read u27) = (BitVec.ofNat 64 middle.2.toNat) := (e27.agrees.read (by simp [mulR64Effect_components])).trans g26r13
  have g24r1 : ((Operand.reg 1 : Operand 64).read u24) = upper.1 := (e24.agrees.read (by simp [adcR64R64Effect_components])).trans g23r1
  have g25r1 : ((Operand.reg 1 : Operand 64).read u25) = upper.1 := (e25.agrees.read (by simp [movR64M64Effect_components])).trans g24r1
  have g26r1 : ((Operand.reg 1 : Operand 64).read u26) = upper.1 := (e26.agrees.read (by simp [movR64R64Effect_components])).trans g25r1
  have g27r1 : ((Operand.reg 1 : Operand 64).read u27) = upper.1 := (e27.agrees.read (by simp [mulR64Effect_components])).trans g26r1
  have g26r5 : ((Operand.reg 5 : Operand 64).read u26) = 0xffffffff00000001 := (e26.agrees.read (by simp [movR64R64Effect_components])).trans g25r5
  have g27r5 : ((Operand.reg 5 : Operand 64).read u27) = 0xffffffff00000001 := (e27.agrees.read (by simp [mulR64Effect_components])).trans g26r5
  have g23r14 : ((Operand.reg 14 : Operand 64).read u23) = d := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r14
  have g24r14 : ((Operand.reg 14 : Operand 64).read u24) = d := (e24.agrees.read (by simp [adcR64R64Effect_components])).trans g23r14
  have g25r14 : ((Operand.reg 14 : Operand 64).read u25) = d := (e25.agrees.read (by simp [movR64M64Effect_components])).trans g24r14
  have g26r14 : ((Operand.reg 14 : Operand 64).read u26) = d := (e26.agrees.read (by simp [movR64R64Effect_components])).trans g25r14
  have g27r14 : ((Operand.reg 14 : Operand 64).read u27) = d := (e27.agrees.read (by simp [mulR64Effect_components])).trans g26r14
  have g23r9 : ((Operand.reg 9 : Operand 64).read u23) = extra := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r9
  have g24r9 : ((Operand.reg 9 : Operand 64).read u24) = extra := (e24.agrees.read (by simp [adcR64R64Effect_components])).trans g23r9
  have g25r9 : ((Operand.reg 9 : Operand 64).read u25) = extra := (e25.agrees.read (by simp [movR64M64Effect_components])).trans g24r9
  have g26r9 : ((Operand.reg 9 : Operand 64).read u26) = extra := (e26.agrees.read (by simp [movR64R64Effect_components])).trans g25r9
  have g27r9 : ((Operand.reg 9 : Operand 64).read u27) = extra := (e27.agrees.read (by simp [mulR64Effect_components])).trans g26r9
  have g19r7 : ((Operand.reg 7 : Operand 64).read u19) = s.regValue .rdi := (e19.agrees.read (by simp [xorR32R32Effect_components])).trans g18r7
  have g20r7 : ((Operand.reg 7 : Operand 64).read u20) = s.regValue .rdi := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r7
  have g21r7 : ((Operand.reg 7 : Operand 64).read u21) = s.regValue .rdi := (e21.agrees.read (by simp [setccR8Effect_components])).trans g20r7
  have g22r7 : ((Operand.reg 7 : Operand 64).read u22) = s.regValue .rdi := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r7
  have g23r7 : ((Operand.reg 7 : Operand 64).read u23) = s.regValue .rdi := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r7
  have g24r7 : ((Operand.reg 7 : Operand 64).read u24) = s.regValue .rdi := (e24.agrees.read (by simp [adcR64R64Effect_components])).trans g23r7
  have g25r7 : ((Operand.reg 7 : Operand 64).read u25) = s.regValue .rdi := (e25.agrees.read (by simp [movR64M64Effect_components])).trans g24r7
  have g26r7 : ((Operand.reg 7 : Operand 64).read u26) = s.regValue .rdi := (e26.agrees.read (by simp [movR64R64Effect_components])).trans g25r7
  have g27r7 : ((Operand.reg 7 : Operand 64).read u27) = s.regValue .rdi := (e27.agrees.read (by simp [mulR64Effect_components])).trans g26r7
  have g19r6 : ((Operand.reg 6 : Operand 64).read u19) = 0xffffffff := (e19.agrees.read (by simp [xorR32R32Effect_components])).trans g18r6
  have g20r6 : ((Operand.reg 6 : Operand 64).read u20) = 0xffffffff := (e20.agrees.read (by simp [addR64R64Effect_components])).trans g19r6
  have g21r6 : ((Operand.reg 6 : Operand 64).read u21) = 0xffffffff := (e21.agrees.read (by simp [setccR8Effect_components])).trans g20r6
  have g22r6 : ((Operand.reg 6 : Operand 64).read u22) = 0xffffffff := (e22.agrees.read (by simp [addR64R64Effect_components])).trans g21r6
  have g23r6 : ((Operand.reg 6 : Operand 64).read u23) = 0xffffffff := (e23.agrees.read (by simp [leaR64Effect_components])).trans g22r6
  have g24r6 : ((Operand.reg 6 : Operand 64).read u24) = 0xffffffff := (e24.agrees.read (by simp [adcR64R64Effect_components])).trans g23r6
  have g25r6 : ((Operand.reg 6 : Operand 64).read u25) = 0xffffffff := (e25.agrees.read (by simp [movR64M64Effect_components])).trans g24r6
  have g26r6 : ((Operand.reg 6 : Operand 64).read u26) = 0xffffffff := (e26.agrees.read (by simp [movR64R64Effect_components])).trans g25r6
  have g27r6 : ((Operand.reg 6 : Operand 64).read u27) = 0xffffffff := (e27.agrees.read (by simp [mulR64Effect_components])).trans g26r6
  exact ⟨u27, ⟨fuelLow + 9, (((((((((runLow.trans run19).trans run20).trans run21).trans run22).trans run23).trans run24).trans run25).trans run26).trans run27)⟩, ⟨f27, e27.rip, m27, (by change ((Operand.reg 12 : Operand 64).read u27) = (thirdLow a b).1; rw [lowWords]; exact g27r12), (by change ((Operand.reg 15 : Operand 64).read u27) = (add64 (thirdLow a b).2 c).1; rw [lowWords, eq_middle]; exact g27r15), (by change ((Operand.reg 13 : Operand 64).read u27) = BitVec.ofNat 64 (add64 (thirdLow a b).2 c).2.toNat; rw [lowWords, eq_middle]; exact g27r13), (by change ((Operand.reg 1 : Operand 64).read u27) = (add64 d extra).1; rw [eq_upper]; exact g27r1), (by change ((Operand.reg 0 : Operand 64).read u27) = (product64 0xffffffff00000001 a).1; rw [eq_p3]; exact g27r0), (by change ((Operand.reg 2 : Operand 64).read u27) = (product64 0xffffffff00000001 a).2; rw [eq_p3]; exact g27r2), g27r5, g27r14, g27r9, g27r7, g27r6⟩⟩


end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper
