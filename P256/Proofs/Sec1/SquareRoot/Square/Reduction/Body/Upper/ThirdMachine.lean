import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.ThirdMiddle

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
theorem third_machine [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : Second s t v) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ ThirdMachine s t u := by
  let a := t.regValue .r13
  let b := t.regValue .rbp
  let c := t.regValue .rbx
  let d := t.regValue .r14
  let extra := t.regValue .r9
  let carry := (carryByte s t).setWidth 64
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
  generalize eq_q : add64 (BitVec.ofNat 64 middle.2.toNat) upper.1 = q
  generalize eq_r : add64 q.1 p3.1 = r
  generalize eq_rh : adc64 (BitVec.ofNat 64 q.2.toNat) p3.2 r.2 = rh
  generalize eq_top : adc64 carry rh.1 upper.2 = top

  as_aux_lemma =>
    have lowWords : thirdLow a b = (y.1, k.1) := by
      as_aux_lemma =>
        simp only [thirdLow, eq_p0, eq_p1, eq_x, eq_h, eq_z, eq_y, eq_k]
    have model : thirdWords ⟨a, b, c, d⟩ extra carry = (⟨y.1, middle.1, r.1, top.1⟩, top.2) := by
      as_aux_lemma =>
        simp only [thirdWords, lowWords, highWords, eq_middle, eq_upper, eq_p3, eq_q, eq_r, eq_rh, eq_top]
    obtain ⟨u27, ⟨fuelMiddle, runMiddle⟩, mid⟩ := third_machine_middle pre state
    have f27 : ScalarFrame.FrameState s u27 32 112 112 := by
      as_aux_lemma =>
        exact mid.frame
    have m27 := mid.memory
    have g27r12 : ((Operand.reg 12 : Operand 64).read u27) = y.1 := by
      as_aux_lemma =>
        have h := mid.r12; change ((Operand.reg 12 : Operand 64).read u27) = (thirdLow a b).1 at h; rw [lowWords] at h; exact h
    have g27r15 : ((Operand.reg 15 : Operand 64).read u27) = middle.1 := by
      as_aux_lemma =>
        have h := mid.r15; change ((Operand.reg 15 : Operand 64).read u27) = (add64 (thirdLow a b).2 c).1 at h; rw [lowWords, eq_middle] at h; exact h
    have g27r13 : ((Operand.reg 13 : Operand 64).read u27) = (BitVec.ofNat 64 middle.2.toNat) := by
      as_aux_lemma =>
        have h := mid.r13; change ((Operand.reg 13 : Operand 64).read u27) = BitVec.ofNat 64 (add64 (thirdLow a b).2 c).2.toNat at h; rw [lowWords, eq_middle] at h; exact h
    have g27r1 : ((Operand.reg 1 : Operand 64).read u27) = upper.1 := by
      as_aux_lemma =>
        have h := mid.rcx; change ((Operand.reg 1 : Operand 64).read u27) = (add64 d extra).1 at h; rw [eq_upper] at h; exact h
    have g27r0 : ((Operand.reg 0 : Operand 64).read u27) = p3.1 := by
      as_aux_lemma =>
        have h := mid.rax; change ((Operand.reg 0 : Operand 64).read u27) = (product64 0xffffffff00000001 a).1 at h; rw [eq_p3] at h; exact h
    have g27r2 : ((Operand.reg 2 : Operand 64).read u27) = p3.2 := by
      as_aux_lemma =>
        have h := mid.rdx; change ((Operand.reg 2 : Operand 64).read u27) = (product64 0xffffffff00000001 a).2 at h; rw [eq_p3] at h; exact h
    have g27r5 : ((Operand.reg 5 : Operand 64).read u27) = 0xffffffff00000001 := by
      as_aux_lemma =>
        exact mid.rbp
    have g27r14 : ((Operand.reg 14 : Operand 64).read u27) = d := mid.r14
    have g27r9 : ((Operand.reg 9 : Operand 64).read u27) = extra := mid.r9
    have g27r7 : ((Operand.reg 7 : Operand 64).read u27) = s.regValue .rdi := by
      as_aux_lemma =>
        exact mid.rdi
    have g27r6 : ((Operand.reg 6 : Operand 64).read u27) = 0xffffffff := by
      as_aux_lemma =>
        exact mid.rsi
    obtain ⟨u28, run28, ready28, e28⟩ :=
      (xor_r32_r32_rex_effect_step 0x11356c 0x45 0xc0 (by simp [RexNoWPrefix]) (by decide)).advances (readyToStep f27.machine f27.bindingsSupported)
        (programText_slice (programLoaded_codeIn f27.loaded) 0x1356c _ (by decide) (by decide +kernel))
        mid.rip
        (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1356f (by decide)))
    change (xorR32R32Effect 0x11356c 3 8 8 u27).Holds u27 u28 at e28
    have f28 : ScalarFrame.FrameState s u28 32 112 112 := by
      as_aux_lemma =>
        exact f27.after_registers ready28 e28.agrees (by simp [xorR32R32Effect_components, Component.Covers]) (by simp [xorR32R32Effect_components])
    have m28 : u28.external = t.external := by
      as_aux_lemma =>
        exact (e28.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])).trans m27
    have g28r8 : ((Operand.reg 8 : Operand 64).read u28) = 0 := by
      as_aux_lemma =>
        simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, Write.AllHold] using e28.writes
    have g28r1 : ((Operand.reg 1 : Operand 64).read u28) = upper.1 := by
      as_aux_lemma =>
        exact (e28.agrees.read (by simp [xorR32R32Effect_components])).trans g27r1
    have g28r13 : ((Operand.reg 13 : Operand 64).read u28) = (BitVec.ofNat 64 middle.2.toNat) := by
      as_aux_lemma =>
        exact (e28.agrees.read (by simp [xorR32R32Effect_components])).trans g27r13
    obtain ⟨u29, run29, ready29, e29⟩ :=
      (add_r64_r64_effect_step 0x11356f 0x49 0xcd (by simp [RexWPrefix]) (by decide)).advances (readyToStep f28.machine f28.bindingsSupported)
        (programText_slice (programLoaded_codeIn f28.loaded) 0x1356f _ (by decide) (by decide +kernel))
        e28.rip
        (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13572 (by decide)))
    change (addR64R64Effect 0x11356f 13 1 u28).Holds u28 u29 at e29
    have f29 : ScalarFrame.FrameState s u29 32 112 112 := by
      as_aux_lemma =>
        exact f28.after_registers ready29 e29.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
    have m29 : u29.external = t.external := by
      as_aux_lemma =>
        exact (e29.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans m28
    have g29r13 : ((Operand.reg 13 : Operand 64).read u29) = q.1 := by
      as_aux_lemma =>
        have h := e29.writes
        change ((Operand.reg 13 : Operand 64).read u29) = (addSpec ((Operand.reg 13 : Operand 64).read u28) ((Operand.reg 1 : Operand 64).read u28)).1 at h
        rw [g28r1, g28r13] at h
        simpa only [← eq_q, add64] using h
    have cf29 : (StatusFlags.ofRFLAGS u29.RFLAGS).CF = q.2 := by
      as_aux_lemma =>
        have h := e29.flags.1
        change (StatusFlags.ofRFLAGS u29.RFLAGS).CF = (addSpec ((Operand.reg 13 : Operand 64).read u28) ((Operand.reg 1 : Operand 64).read u28)).2.CF at h
        rw [g28r1, g28r13] at h
        simpa only [← eq_q, add64] using h
    have g29r8 : ((Operand.reg 8 : Operand 64).read u29) = 0 := by
      as_aux_lemma =>
        exact (e29.agrees.read (by simp [addR64R64Effect_components])).trans g28r8
    obtain ⟨u30, run30, ready30, e30⟩ :=
      (setcc_r8_rex_effect_step 0x113572 0x41 0x92 0xc0 (by simp [RexPrefix]) (.inl rfl) (by decide)).advances (readyToStep f29.machine f29.bindingsSupported)
        (programText_slice (programLoaded_codeIn f29.loaded) 0x13572 _ (by decide) (by decide +kernel))
        e29.rip
        (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13576 (by decide)))
    change (setccR8Effect 0x113572 4 8 2 u29).Holds u29 u30 at e30
    have f30 : ScalarFrame.FrameState s u30 32 112 112 := by
      as_aux_lemma =>
        exact f29.after_registers ready30 e30.agrees (by simp [setccR8Effect_components, Component.Covers]) (by simp [setccR8Effect_components])
    have m30 : u30.external = t.external := by
      as_aux_lemma =>
        exact (e30.agrees.external (by simp [setccR8Effect_components, Component.Covers])).trans m29
    have g30r8 : ((Operand.reg 8 : Operand 64).read u30) = (BitVec.ofNat 64 q.2.toNat) := by
      as_aux_lemma =>
        have h := e30.writes
        change ((Operand.reg 8 : Operand 64).read u30) = mergeGPR 8 (if (StatusFlags.ofRFLAGS u29.RFLAGS).CF then 1 else 0) ((Operand.reg 8 : Operand 64).read u29) at h
        rw [g29r8, cf29] at h
        simpa only [BitVec.ofNat_eq_ofNat, P256.Proofs.Field.Subtract.setb_zero_value] using h
    have g28r0 : ((Operand.reg 0 : Operand 64).read u28) = p3.1 := by
      as_aux_lemma =>
        exact (e28.agrees.read (by simp [xorR32R32Effect_components])).trans g27r0
    have g29r0 : ((Operand.reg 0 : Operand 64).read u29) = p3.1 := by
      as_aux_lemma =>
        exact (e29.agrees.read (by simp [addR64R64Effect_components])).trans g28r0
    have g30r0 : ((Operand.reg 0 : Operand 64).read u30) = p3.1 := by
      as_aux_lemma =>
        exact (e30.agrees.read (by simp [setccR8Effect_components])).trans g29r0
    have g30r13 : ((Operand.reg 13 : Operand 64).read u30) = q.1 := by
      as_aux_lemma =>
        exact (e30.agrees.read (by simp [setccR8Effect_components])).trans g29r13
    obtain ⟨u31, run31, ready31, e31⟩ :=
      (add_r64_r64_effect_step 0x113576 0x49 0xc5 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f30.machine f30.bindingsSupported)
        (programText_slice (programLoaded_codeIn f30.loaded) 0x13576 _ (by decide) (by decide +kernel))
        e30.rip
        (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13579 (by decide)))
    change (addR64R64Effect 0x113576 13 0 u30).Holds u30 u31 at e31
    have f31 : ScalarFrame.FrameState s u31 32 112 112 := by
      as_aux_lemma =>
        exact f30.after_registers ready31 e31.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
    have m31 : u31.external = t.external := by
      as_aux_lemma =>
        exact (e31.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans m30
    have g31r13 : ((Operand.reg 13 : Operand 64).read u31) = r.1 := by
      as_aux_lemma =>
        have h := e31.writes
        change ((Operand.reg 13 : Operand 64).read u31) = (addSpec ((Operand.reg 13 : Operand 64).read u30) ((Operand.reg 0 : Operand 64).read u30)).1 at h
        rw [g30r0, g30r13] at h
        simpa only [← eq_r, add64] using h
    have cf31 : (StatusFlags.ofRFLAGS u31.RFLAGS).CF = r.2 := by
      as_aux_lemma =>
        have h := e31.flags.1
        change (StatusFlags.ofRFLAGS u31.RFLAGS).CF = (addSpec ((Operand.reg 13 : Operand 64).read u30) ((Operand.reg 0 : Operand 64).read u30)).2.CF at h
        rw [g30r0, g30r13] at h
        simpa only [← eq_r, add64] using h
    have g28r2 : ((Operand.reg 2 : Operand 64).read u28) = p3.2 := by
      as_aux_lemma =>
        exact (e28.agrees.read (by simp [xorR32R32Effect_components])).trans g27r2
    have g29r2 : ((Operand.reg 2 : Operand 64).read u29) = p3.2 := by
      as_aux_lemma =>
        exact (e29.agrees.read (by simp [addR64R64Effect_components])).trans g28r2
    have g30r2 : ((Operand.reg 2 : Operand 64).read u30) = p3.2 := by
      as_aux_lemma =>
        exact (e30.agrees.read (by simp [setccR8Effect_components])).trans g29r2
    have g31r2 : ((Operand.reg 2 : Operand 64).read u31) = p3.2 := by
      as_aux_lemma =>
        exact (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r2
    have g31r8 : ((Operand.reg 8 : Operand 64).read u31) = (BitVec.ofNat 64 q.2.toNat) := by
      as_aux_lemma =>
        exact (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r8
    obtain ⟨u32, run32, ready32, e32⟩ :=
      (adc_r64_r64_effect_step 0x113579 0x49 0xd0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f31.machine f31.bindingsSupported)
        (programText_slice (programLoaded_codeIn f31.loaded) 0x13579 _ (by decide) (by decide +kernel))
        e31.rip
        (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1357c (by decide)))
    change (adcR64R64Effect 0x113579 8 2 u31).Holds u31 u32 at e32
    have f32 : ScalarFrame.FrameState s u32 32 112 112 := by
      as_aux_lemma =>
        exact f31.after_registers ready32 e32.agrees (by simp [adcR64R64Effect_components, Component.Covers]) (by simp [adcR64R64Effect_components])
    have m32 : u32.external = t.external := by
      as_aux_lemma =>
        exact (e32.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans m31
    have g32r8 : ((Operand.reg 8 : Operand 64).read u32) = rh.1 := by
      as_aux_lemma =>
        have h := e32.writes
        change ((Operand.reg 8 : Operand 64).read u32) = (adcSpec ((Operand.reg 8 : Operand 64).read u31) ((Operand.reg 2 : Operand 64).read u31) (u31.RFLAGS.extractLsb' 0 1)).1 at h
        rw [g31r2, g31r8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf31] at h
        simpa only [← eq_rh, adc64] using h
    have cf32 : (StatusFlags.ofRFLAGS u32.RFLAGS).CF = rh.2 := by
      as_aux_lemma =>
        have h := e32.flags.1
        change (StatusFlags.ofRFLAGS u32.RFLAGS).CF = (adcSpec ((Operand.reg 8 : Operand 64).read u31) ((Operand.reg 2 : Operand 64).read u31) (u31.RFLAGS.extractLsb' 0 1)).2.CF at h
        rw [g31r2, g31r8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf31] at h
        simpa only [← eq_rh, adc64] using h
    have g28r9 : ((Operand.reg 9 : Operand 64).read u28) = extra := by
      as_aux_lemma =>
        exact (e28.agrees.read (by simp [xorR32R32Effect_components])).trans g27r9
    have g29r9 : ((Operand.reg 9 : Operand 64).read u29) = extra := by
      as_aux_lemma =>
        exact (e29.agrees.read (by simp [addR64R64Effect_components])).trans g28r9
    have g30r9 : ((Operand.reg 9 : Operand 64).read u30) = extra := by
      as_aux_lemma =>
        exact (e30.agrees.read (by simp [setccR8Effect_components])).trans g29r9
    have g31r9 : ((Operand.reg 9 : Operand 64).read u31) = extra := by
      as_aux_lemma =>
        exact (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r9
    have g32r9 : ((Operand.reg 9 : Operand 64).read u32) = extra := by
      as_aux_lemma =>
        exact (e32.agrees.read (by simp [adcR64R64Effect_components])).trans g31r9
    have g28r14 : ((Operand.reg 14 : Operand 64).read u28) = d := by
      as_aux_lemma =>
        exact (e28.agrees.read (by simp [xorR32R32Effect_components])).trans g27r14
    have g29r14 : ((Operand.reg 14 : Operand 64).read u29) = d := by
      as_aux_lemma =>
        exact (e29.agrees.read (by simp [addR64R64Effect_components])).trans g28r14
    have g30r14 : ((Operand.reg 14 : Operand 64).read u30) = d := by
      as_aux_lemma =>
        exact (e30.agrees.read (by simp [setccR8Effect_components])).trans g29r14
    have g31r14 : ((Operand.reg 14 : Operand 64).read u31) = d := by
      as_aux_lemma =>
        exact (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r14
    have g32r14 : ((Operand.reg 14 : Operand 64).read u32) = d := by
      as_aux_lemma =>
        exact (e32.agrees.read (by simp [adcR64R64Effect_components])).trans g31r14
    obtain ⟨u33, run33, ready33, e33⟩ :=
      (add_r64_r64_effect_step 0x11357c 0x4d 0xce (by simp [RexWPrefix]) (by decide)).advances (readyToStep f32.machine f32.bindingsSupported)
        (programText_slice (programLoaded_codeIn f32.loaded) 0x1357c _ (by decide) (by decide +kernel))
        e32.rip
        (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1357f (by decide)))
    change (addR64R64Effect 0x11357c 14 9 u32).Holds u32 u33 at e33
    have f33 : ScalarFrame.FrameState s u33 32 112 112 := by
      as_aux_lemma =>
        exact f32.after_registers ready33 e33.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
    have m33 : u33.external = t.external := by
      as_aux_lemma =>
        exact (e33.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans m32
    have g33r14 : ((Operand.reg 14 : Operand 64).read u33) = upper.1 := by
      as_aux_lemma =>
        have h := e33.writes
        change ((Operand.reg 14 : Operand 64).read u33) = (addSpec ((Operand.reg 14 : Operand 64).read u32) ((Operand.reg 9 : Operand 64).read u32)).1 at h
        rw [g32r9, g32r14] at h
        simpa only [← eq_upper, add64] using h
    have cf33 : (StatusFlags.ofRFLAGS u33.RFLAGS).CF = upper.2 := by
      as_aux_lemma =>
        have h := e33.flags.1
        change (StatusFlags.ofRFLAGS u33.RFLAGS).CF = (addSpec ((Operand.reg 14 : Operand 64).read u32) ((Operand.reg 9 : Operand 64).read u32)).2.CF at h
        rw [g32r9, g32r14] at h
        simpa only [← eq_upper, add64] using h
    obtain ⟨u34, run34, ready34, e34⟩ :=
      (movzx_r_m8_rex_effect_step 0x11357f 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (by intro; rfl) 1 (.sib 4 none 0 (.d8 7)) (by decide) rfl rfl).advances (readyToStep f33.machine f33.bindingsSupported)
        (programText_slice (programLoaded_codeIn f33.loaded) 0x1357f _ (by decide) (by decide +kernel))
        ⟨e33.rip, ScalarFrame.stack_readable pre.toCalleePre f33 (offset := 7) (len := 1) (by decide) (by decide)⟩
        (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13585 (by decide)))
    change (movzxR32M8Effect 0x11357f 6 9 (.sib 4 none 0 (.d8 7)) u33).Holds u33 u34 at e34
    have f34 : ScalarFrame.FrameState s u34 32 112 112 := by
      as_aux_lemma =>
        exact f33.after_registers ready34 e34.agrees (by simp [movzxR32M8Effect_components, Component.Covers]) (by simp [movzxR32M8Effect_components])
    have m34 : u34.external = t.external := by
      as_aux_lemma =>
        exact (e34.agrees.external (by simp [movzxR32M8Effect_components, Component.Covers])).trans m33
    have g34r9 : ((Operand.reg 9 : Operand 64).read u34) = carry := by
      as_aux_lemma =>
        have h := e34.writes
        change ((Operand.reg 9 : Operand 64).read u34) = (memLoad u33.external (stackPtr u33 + 7) 8).setWidth 64 at h
        rw [f33.rsp, m33] at h
        exact h
    have g33r8 : ((Operand.reg 8 : Operand 64).read u33) = rh.1 := by
      as_aux_lemma =>
        exact (e33.agrees.read (by simp [addR64R64Effect_components])).trans g32r8
    have g34r8 : ((Operand.reg 8 : Operand 64).read u34) = rh.1 := by
      as_aux_lemma =>
        exact (e34.agrees.read (by simp [movzxR32M8Effect_components])).trans g33r8
    have cf34 : (StatusFlags.ofRFLAGS u34.RFLAGS).CF = upper.2 := by
      as_aux_lemma =>
        rw [e34.agrees.statusFlags (by simp [movzxR32M8Effect_components]), cf33]
    obtain ⟨u35, run35, ready35, e35⟩ :=
      (adc_r64_r64_effect_step 0x113585 0x4d 0xc1 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f34.machine f34.bindingsSupported)
        (programText_slice (programLoaded_codeIn f34.loaded) 0x13585 _ (by decide) (by decide +kernel))
        e34.rip
        (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13588 (by decide)))
    change (adcR64R64Effect 0x113585 9 8 u34).Holds u34 u35 at e35
    have f35 : ScalarFrame.FrameState s u35 32 112 112 := by
      as_aux_lemma =>
        exact f34.after_registers ready35 e35.agrees (by simp [adcR64R64Effect_components, Component.Covers]) (by simp [adcR64R64Effect_components])
    have m35 : u35.external = t.external := by
      as_aux_lemma =>
        exact (e35.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans m34
    have g35r9 : ((Operand.reg 9 : Operand 64).read u35) = top.1 := by
      as_aux_lemma =>
        have h := e35.writes
        change ((Operand.reg 9 : Operand 64).read u35) = (adcSpec ((Operand.reg 9 : Operand 64).read u34) ((Operand.reg 8 : Operand 64).read u34) (u34.RFLAGS.extractLsb' 0 1)).1 at h
        rw [g34r8, g34r9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf34] at h
        simpa only [← eq_top, adc64] using h
    have cf35 : (StatusFlags.ofRFLAGS u35.RFLAGS).CF = top.2 := by
      as_aux_lemma =>
        have h := e35.flags.1
        change (StatusFlags.ofRFLAGS u35.RFLAGS).CF = (adcSpec ((Operand.reg 9 : Operand 64).read u34) ((Operand.reg 8 : Operand 64).read u34) (u34.RFLAGS.extractLsb' 0 1)).2.CF at h
        rw [g34r8, g34r9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf34] at h
        simpa only [← eq_top, adc64] using h
    have g28r12 : ((Operand.reg 12 : Operand 64).read u28) = y.1 := by
      as_aux_lemma =>
        exact (e28.agrees.read (by simp [xorR32R32Effect_components])).trans g27r12
    have g29r12 : ((Operand.reg 12 : Operand 64).read u29) = y.1 := by
      as_aux_lemma =>
        exact (e29.agrees.read (by simp [addR64R64Effect_components])).trans g28r12
    have g30r12 : ((Operand.reg 12 : Operand 64).read u30) = y.1 := by
      as_aux_lemma =>
        exact (e30.agrees.read (by simp [setccR8Effect_components])).trans g29r12
    have g31r12 : ((Operand.reg 12 : Operand 64).read u31) = y.1 := by
      as_aux_lemma =>
        exact (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r12
    have g32r12 : ((Operand.reg 12 : Operand 64).read u32) = y.1 := by
      as_aux_lemma =>
        exact (e32.agrees.read (by simp [adcR64R64Effect_components])).trans g31r12
    have g33r12 : ((Operand.reg 12 : Operand 64).read u33) = y.1 := by
      as_aux_lemma =>
        exact (e33.agrees.read (by simp [addR64R64Effect_components])).trans g32r12
    have g34r12 : ((Operand.reg 12 : Operand 64).read u34) = y.1 := by
      as_aux_lemma =>
        exact (e34.agrees.read (by simp [movzxR32M8Effect_components])).trans g33r12
    have g35r12 : ((Operand.reg 12 : Operand 64).read u35) = y.1 := by
      as_aux_lemma =>
        exact (e35.agrees.read (by simp [adcR64R64Effect_components])).trans g34r12
    have g28r15 : ((Operand.reg 15 : Operand 64).read u28) = middle.1 := by
      as_aux_lemma =>
        exact (e28.agrees.read (by simp [xorR32R32Effect_components])).trans g27r15
    have g29r15 : ((Operand.reg 15 : Operand 64).read u29) = middle.1 := by
      as_aux_lemma =>
        exact (e29.agrees.read (by simp [addR64R64Effect_components])).trans g28r15
    have g30r15 : ((Operand.reg 15 : Operand 64).read u30) = middle.1 := by
      as_aux_lemma =>
        exact (e30.agrees.read (by simp [setccR8Effect_components])).trans g29r15
    have g31r15 : ((Operand.reg 15 : Operand 64).read u31) = middle.1 := by
      as_aux_lemma =>
        exact (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r15
    have g32r15 : ((Operand.reg 15 : Operand 64).read u32) = middle.1 := by
      as_aux_lemma =>
        exact (e32.agrees.read (by simp [adcR64R64Effect_components])).trans g31r15
    have g33r15 : ((Operand.reg 15 : Operand 64).read u33) = middle.1 := by
      as_aux_lemma =>
        exact (e33.agrees.read (by simp [addR64R64Effect_components])).trans g32r15
    have g34r15 : ((Operand.reg 15 : Operand 64).read u34) = middle.1 := by
      as_aux_lemma =>
        exact (e34.agrees.read (by simp [movzxR32M8Effect_components])).trans g33r15
    have g35r15 : ((Operand.reg 15 : Operand 64).read u35) = middle.1 := by
      as_aux_lemma =>
        exact (e35.agrees.read (by simp [adcR64R64Effect_components])).trans g34r15
    have g32r13 : ((Operand.reg 13 : Operand 64).read u32) = r.1 := by
      as_aux_lemma =>
        exact (e32.agrees.read (by simp [adcR64R64Effect_components])).trans g31r13
    have g33r13 : ((Operand.reg 13 : Operand 64).read u33) = r.1 := by
      as_aux_lemma =>
        exact (e33.agrees.read (by simp [addR64R64Effect_components])).trans g32r13
    have g34r13 : ((Operand.reg 13 : Operand 64).read u34) = r.1 := by
      as_aux_lemma =>
        exact (e34.agrees.read (by simp [movzxR32M8Effect_components])).trans g33r13
    have g35r13 : ((Operand.reg 13 : Operand 64).read u35) = r.1 := by
      as_aux_lemma =>
        exact (e35.agrees.read (by simp [adcR64R64Effect_components])).trans g34r13
    have g28r7 : ((Operand.reg 7 : Operand 64).read u28) = s.regValue .rdi := by
      as_aux_lemma =>
        exact (e28.agrees.read (by simp [xorR32R32Effect_components])).trans g27r7
    have g29r7 : ((Operand.reg 7 : Operand 64).read u29) = s.regValue .rdi := by
      as_aux_lemma =>
        exact (e29.agrees.read (by simp [addR64R64Effect_components])).trans g28r7
    have g30r7 : ((Operand.reg 7 : Operand 64).read u30) = s.regValue .rdi := by
      as_aux_lemma =>
        exact (e30.agrees.read (by simp [setccR8Effect_components])).trans g29r7
    have g31r7 : ((Operand.reg 7 : Operand 64).read u31) = s.regValue .rdi := by
      as_aux_lemma =>
        exact (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r7
    have g32r7 : ((Operand.reg 7 : Operand 64).read u32) = s.regValue .rdi := by
      as_aux_lemma =>
        exact (e32.agrees.read (by simp [adcR64R64Effect_components])).trans g31r7
    have g33r7 : ((Operand.reg 7 : Operand 64).read u33) = s.regValue .rdi := by
      as_aux_lemma =>
        exact (e33.agrees.read (by simp [addR64R64Effect_components])).trans g32r7
    have g34r7 : ((Operand.reg 7 : Operand 64).read u34) = s.regValue .rdi := by
      as_aux_lemma =>
        exact (e34.agrees.read (by simp [movzxR32M8Effect_components])).trans g33r7
    have g35r7 : ((Operand.reg 7 : Operand 64).read u35) = s.regValue .rdi := by
      as_aux_lemma =>
        exact (e35.agrees.read (by simp [adcR64R64Effect_components])).trans g34r7
    have g28r6 : ((Operand.reg 6 : Operand 64).read u28) = 0xffffffff := by
      as_aux_lemma =>
        exact (e28.agrees.read (by simp [xorR32R32Effect_components])).trans g27r6
    have g29r6 : ((Operand.reg 6 : Operand 64).read u29) = 0xffffffff := by
      as_aux_lemma =>
        exact (e29.agrees.read (by simp [addR64R64Effect_components])).trans g28r6
    have g30r6 : ((Operand.reg 6 : Operand 64).read u30) = 0xffffffff := by
      as_aux_lemma =>
        exact (e30.agrees.read (by simp [setccR8Effect_components])).trans g29r6
    have g31r6 : ((Operand.reg 6 : Operand 64).read u31) = 0xffffffff := by
      as_aux_lemma =>
        exact (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r6
    have g32r6 : ((Operand.reg 6 : Operand 64).read u32) = 0xffffffff := by
      as_aux_lemma =>
        exact (e32.agrees.read (by simp [adcR64R64Effect_components])).trans g31r6
    have g33r6 : ((Operand.reg 6 : Operand 64).read u33) = 0xffffffff := by
      as_aux_lemma =>
        exact (e33.agrees.read (by simp [addR64R64Effect_components])).trans g32r6
    have g34r6 : ((Operand.reg 6 : Operand 64).read u34) = 0xffffffff := by
      as_aux_lemma =>
        exact (e34.agrees.read (by simp [movzxR32M8Effect_components])).trans g33r6
    have g35r6 : ((Operand.reg 6 : Operand 64).read u35) = 0xffffffff := by
      as_aux_lemma =>
        exact (e35.agrees.read (by simp [adcR64R64Effect_components])).trans g34r6
    have g28r5 : ((Operand.reg 5 : Operand 64).read u28) = 0xffffffff00000001 := by
      as_aux_lemma =>
        exact (e28.agrees.read (by simp [xorR32R32Effect_components])).trans g27r5
    have g29r5 : ((Operand.reg 5 : Operand 64).read u29) = 0xffffffff00000001 := by
      as_aux_lemma =>
        exact (e29.agrees.read (by simp [addR64R64Effect_components])).trans g28r5
    have g30r5 : ((Operand.reg 5 : Operand 64).read u30) = 0xffffffff00000001 := by
      as_aux_lemma =>
        exact (e30.agrees.read (by simp [setccR8Effect_components])).trans g29r5
    have g31r5 : ((Operand.reg 5 : Operand 64).read u31) = 0xffffffff00000001 := by
      as_aux_lemma =>
        exact (e31.agrees.read (by simp [addR64R64Effect_components])).trans g30r5
    have g32r5 : ((Operand.reg 5 : Operand 64).read u32) = 0xffffffff00000001 := by
      as_aux_lemma =>
        exact (e32.agrees.read (by simp [adcR64R64Effect_components])).trans g31r5
    have g33r5 : ((Operand.reg 5 : Operand 64).read u33) = 0xffffffff00000001 := by
      as_aux_lemma =>
        exact (e33.agrees.read (by simp [addR64R64Effect_components])).trans g32r5
    have g34r5 : ((Operand.reg 5 : Operand 64).read u34) = 0xffffffff00000001 := by
      as_aux_lemma =>
        exact (e34.agrees.read (by simp [movzxR32M8Effect_components])).trans g33r5
    have g35r5 : ((Operand.reg 5 : Operand 64).read u35) = 0xffffffff00000001 := by
      as_aux_lemma =>
        exact (e35.agrees.read (by simp [adcR64R64Effect_components])).trans g34r5
    obtain ⟨u36, run36, ready36, e36⟩ :=
      (setcc_m8_effect_step 0x113588 0x92 (.inl rfl) 0 (.sib 4 none 0 (.d8 7))
        (by decide) rfl rfl).advances (readyToStep f35.machine f35.bindingsSupported)
        (programText_slice (programLoaded_codeIn f35.loaded) 0x13588 _ (by decide) (by decide +kernel))
        ⟨e35.rip, by
          have hw := ScalarFrame.stack_writable pre.toCalleePre f35 (offset := 7) (len := 1)
            (by decide) (by decide) (by decide)
          exact ⟨hw.low, hw.mem, hw.tables⟩,
          ScalarFrame.stack_code pre.toCalleePre f35 (offset := 7) (len := 1)
          (codeOffset := 0x13588) (codeLen := 5) (by decide) (by decide) (by decide)⟩
        (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1358d (by decide)))
    change (setccM8Effect 0x113588 5 (.sib 4 none 0 (.d8 7)) 2 u35).Holds u35 u36 at e36
    have ag36 : AgreesExcept [.mem (stackPtr u35 + 7) 1, .rip] u35 u36 := by
      as_aux_lemma =>
        simpa [setccM8Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
          Disp.value, stackPtr] using e36.agrees
    have f36 : ScalarFrame.FrameState s u36 32 112 112 := by
      as_aux_lemma =>
        apply f35.after_effect pre.toCalleePre (by decide) ready36 ag36 ?_ (by simp)
        intro component hc address ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · refine ⟨ScalarFrame.workRegion s 112, by simp, ?_⟩
          apply ScalarFrame.work_contains pre.toCalleePre (offset := 105) (len := 1)
            (by decide) (by decide)
          change (Component.mem (stackPtr u35 + 7#64) 1).Covers address at ha
          rw [ScalarFrame.scalar_stack_address (frameOffset := 112) f35.rsp
            (offset := 7) (by decide) (by decide)] at ha
          exact ha
        · exact ha.elim
    have byte36 : carryByte s u36 = BitVec.ofNat 8 top.2.toNat := by
      as_aux_lemma =>
        have h := e36.writes
        change memLoad u36.external (stackPtr u35 + 7) 8 =
          (if (StatusFlags.ofRFLAGS u35.RFLAGS).CF then 1 else 0) at h
        rw [f35.rsp, cf35] at h
        exact h.trans (carry_byte_value _)
    have keep (offset : Nat) (ho : 16 ≤ offset) (bound : offset + 8 ≤ 64) :
        slot s u36 offset = slot s t offset := by
      as_aux_lemma =>
        have h : slot s u36 offset = slot s u35 offset := by
          apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag36
          intro i hi component hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · rintro ⟨j, hj, he⟩
            rw [f35.rsp] at he
            exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj)
              (hl := by omega) (by simp only [OffsetsApart, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega) he
          · exact id
        exact h.trans (by simp only [slot, m35])

    have g36r12 : ((Operand.reg 12 : Operand 64).read u36) = y.1 := by
      as_aux_lemma =>
        exact (e36.agrees.read (by simp [setccM8Effect_components])).trans g35r12
    have g36r15 : ((Operand.reg 15 : Operand 64).read u36) = middle.1 := by
      as_aux_lemma =>
        exact (e36.agrees.read (by simp [setccM8Effect_components])).trans g35r15
    have g36r13 : ((Operand.reg 13 : Operand 64).read u36) = r.1 := by
      as_aux_lemma =>
        exact (e36.agrees.read (by simp [setccM8Effect_components])).trans g35r13
    have g36r9 : ((Operand.reg 9 : Operand 64).read u36) = top.1 := by
      as_aux_lemma =>
        exact (e36.agrees.read (by simp [setccM8Effect_components])).trans g35r9
    have g36r7 : ((Operand.reg 7 : Operand 64).read u36) = s.regValue .rdi := by
      as_aux_lemma =>
        exact (e36.agrees.read (by simp [setccM8Effect_components])).trans g35r7
    have g36r6 : ((Operand.reg 6 : Operand 64).read u36) = 0xffffffff := by
      as_aux_lemma =>
        exact (e36.agrees.read (by simp [setccM8Effect_components])).trans g35r6
    have g36r5 : ((Operand.reg 5 : Operand 64).read u36) = 0xffffffff00000001 := by
      as_aux_lemma =>
        exact (e36.agrees.read (by simp [setccM8Effect_components])).trans g35r5
    refine ⟨u36, ⟨fuelMiddle + 9, (((((((((runMiddle.trans run28).trans run29).trans run30).trans run31).trans run32).trans run33).trans run34).trans run35).trans run36)⟩, ⟨f36, e36.rip,
      ⟨(keep 56 (by decide) (by decide)).trans state.slots.p0,
        (keep 48 (by decide) (by decide)).trans state.slots.p1,
        (keep 40 (by decide) (by decide)).trans state.slots.p2,
        (keep 32 (by decide) (by decide)).trans state.slots.p3⟩,
      (keep 16 (by decide) (by decide)).trans state.inverse,
      (keep 24 (by decide) (by decide)).trans state.inputPointer,
      g36r7, g36r6, g36r5, ?_, ?_, ?_⟩⟩
    · rw [byte36]
      rw [BitVec.toNat_ofNat]
      exact Nat.le_trans (Nat.mod_le _ _) (Bool.toNat_le _)
    · change (⟨((Operand.reg 12 : Operand 64).read u36), ((Operand.reg 15 : Operand 64).read u36), ((Operand.reg 13 : Operand 64).read u36), ((Operand.reg 9 : Operand 64).read u36)⟩ : Limbs) = (thirdWords ⟨a, b, c, d⟩ extra carry).1
      rw [g36r12, g36r15, g36r13, g36r9]
      rw [model]
    · rw [byte36]
      change (BitVec.ofNat 8 top.2.toNat).toNat = (thirdWords ⟨a, b, c, d⟩ extra carry).2.toNat
      rw [model]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Bool.toNat_le _) (by decide))

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper
