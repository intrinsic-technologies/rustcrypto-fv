import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Stages
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.First.Support
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.ThirdArithmetic
import P256.Proofs.Common.Instructions.Mul.Memory.Triple
import P256.Proofs.Common.Instructions.Setb.Memory.Triple
import P256.Proofs.Field.Subtract.Correction
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper

open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Field.Montgomery (add64 adc64 product64)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

theorem adc_zero_false_word (a : BitVec 64) :
    (adcSpec a 0 (BitVec.ofBool false)).1 = a := by
  simp [adcSpec]

theorem carry_byte_value (b : Bool) :
    (if b then 1 else 0 : BitVec 8) = BitVec.ofNat 8 b.toNat := by
  cases b <;> rfl

structure ThirdMachine [Bindings] (s t u : RamState) : Prop where
  frame : ScalarFrame.FrameState s u 32 112 112
  rip : u.RIP = 0x11358d
  slots : ModulusSlots s u
  inverse : slot s u 16 = 1
  inputPointer : slot s u 24 = s.regValue .rsi
  rdi : u.regValue .rdi = s.regValue .rdi
  rsi : u.regValue .rsi = 0xffffffff
  rbp : u.regValue .rbp = 0xffffffff00000001
  carry : (carryByte s u).toNat ≤ 1
  words : (⟨u.regValue .r12, u.regValue .r15, u.regValue .r13, u.regValue .r9⟩ : Limbs) =
    (thirdWords ⟨t.regValue .r13, t.regValue .rbp, t.regValue .rbx, t.regValue .r14⟩
      (t.regValue .r9) ((carryByte s t).setWidth 64)).1
  carryValue : (carryByte s u).toNat =
    (thirdWords ⟨t.regValue .r13, t.regValue .rbp, t.regValue .rbx, t.regValue .r14⟩
      (t.regValue .r9) ((carryByte s t).setWidth 64)).2.toNat

structure ThirdMachineLow [Bindings] (s t u : RamState) : Prop where
  frame : ScalarFrame.FrameState s u 32 112 112
  rip : u.RIP = 0x11354d
  memory : u.external = t.external
  r12 : u.regValue .r12 = (thirdLow (t.regValue .r13) (t.regValue .rbp)).1
  r15 : u.regValue .r15 = (thirdLow (t.regValue .r13) (t.regValue .rbp)).2
  r11 : u.regValue .r11 = t.regValue .r13
  rax : u.regValue .rax = 0
  rdx : u.regValue .rdx = 0
  rbx : u.regValue .rbx = t.regValue .rbx
  r14 : u.regValue .r14 = t.regValue .r14
  r9 : u.regValue .r9 = t.regValue .r9
  rdi : u.regValue .rdi = s.regValue .rdi
  rsi : u.regValue .rsi = 0xffffffff

structure ThirdMachineMiddle [Bindings] (s t u : RamState) : Prop where
  frame : ScalarFrame.FrameState s u 32 112 112
  rip : u.RIP = 0x11356c
  memory : u.external = t.external
  r12 : u.regValue .r12 = (thirdLow (t.regValue .r13) (t.regValue .rbp)).1
  r15 : u.regValue .r15 = (add64 (thirdLow (t.regValue .r13) (t.regValue .rbp)).2 (t.regValue .rbx)).1
  r13 : u.regValue .r13 = BitVec.ofNat 64 (add64 (thirdLow (t.regValue .r13) (t.regValue .rbp)).2 (t.regValue .rbx)).2.toNat
  rcx : u.regValue .rcx = (add64 (t.regValue .r14) (t.regValue .r9)).1
  rax : u.regValue .rax = (product64 0xffffffff00000001 (t.regValue .r13)).1
  rdx : u.regValue .rdx = (product64 0xffffffff00000001 (t.regValue .r13)).2
  rbp : u.regValue .rbp = 0xffffffff00000001
  r14 : u.regValue .r14 = t.regValue .r14
  r9 : u.regValue .r9 = t.regValue .r9
  rdi : u.regValue .rdi = s.regValue .rdi
  rsi : u.regValue .rsi = 0xffffffff

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem third_machine_low [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : Second s t v) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ ThirdMachineLow s t u := by
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
  have f0 := state.frame
  have m0 : t.external = t.external := rfl
  have g0r13 : (Operand.reg 13 : Operand 64).read t = a := rfl
  have g0r5 : (Operand.reg 5 : Operand 64).read t = b := rfl
  have g0r3 : (Operand.reg 3 : Operand 64).read t = c := rfl
  have g0r14 : (Operand.reg 14 : Operand 64).read t = d := rfl
  have g0r9 : (Operand.reg 9 : Operand 64).read t = extra := rfl
  have g0r10 : (Operand.reg 10 : Operand 64).read t = 0 := state.r10
  have g0r7 : (Operand.reg 7 : Operand 64).read t = s.regValue .rdi := state.rdi
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_r64_m64_effect_step 0x11350e 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x1350e _ (by decide) (by decide +kernel))
      ⟨state.rip, ScalarFrame.stack_readable pre.toCalleePre f0 (offset := 16) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13513 (by decide)))
  change (movR64M64Effect 0x11350e 11 (.sib 4 none 0 (.d8 16)) t).Holds t u1 at e1
  have f1 := f0.after_registers ready1 e1.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have m1 : u1.external = t.external := (e1.agrees.external (by simp [movR64M64Effect_components, Component.Covers])).trans m0
  have load1 : memLoad t.external (stackPtr t + 16) 64 = 1 := by
    rw [f0.rsp, m0]
    exact state.inverse
  have g1r11 : ((Operand.reg 11 : Operand 64).read u1) = 1 := by
    have h := e1.writes
    change ((Operand.reg 11 : Operand 64).read u1) = memLoad t.external (stackPtr t + 16) 64 at h
    rw [load1] at h
    exact h
  have g1r13 : ((Operand.reg 13 : Operand 64).read u1) = a := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r13
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (imul_r64_r64_effect_step 0x113513 0x4d 0xdd (by simp [RexWPrefix]) (by decide)).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x13513 _ (by decide) (by decide +kernel))
      e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13517 (by decide)))
  change (imulR64R64Effect 0x113513 11 13 u1).Holds u1 u2 at e2
  have f2 := f1.after_registers ready2 e2.agrees (by simp [FirstRound.imulR64R64Effect_components, Component.Covers]) (by simp [FirstRound.imulR64R64Effect_components])
  have m2 : u2.external = t.external := (e2.agrees.external (by simp [FirstRound.imulR64R64Effect_components, Component.Covers])).trans m1
  have g2r11 : ((Operand.reg 11 : Operand 64).read u2) = a := by
    have h := e2.writes
    change ((Operand.reg 11 : Operand 64).read u2) = ((Operand.reg 11 : Operand 64).read u1) * ((Operand.reg 13 : Operand 64).read u1) at h
    rw [g1r13, g1r11] at h
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.one_mul] using h
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (mov_r64_r64_effect_step 0x113517 0x4c 0xd8 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x13517 _ (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1351a (by decide)))
  change (movR64R64Effect 0x113517 0 11 u2).Holds u2 u3 at e3
  have f3 := f2.after_registers ready3 e3.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have m3 : u3.external = t.external := (e3.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans m2
  have g3r0 : ((Operand.reg 0 : Operand 64).read u3) = a := by
    have h := e3.writes
    change ((Operand.reg 0 : Operand 64).read u3) = ((Operand.reg 11 : Operand 64).read u2) at h
    rw [g2r11] at h
    exact h
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (mul_m64_effect_step 0x11351a 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x1351a _ (by decide) (by decide +kernel))
      ⟨e3.rip, ScalarFrame.stack_readable pre.toCalleePre f3 (offset := 56) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1351f (by decide)))
  change (mulM64Effect 0x11351a (.sib 4 none 0 (.d8 56)) u3).Holds u3 u4 at e4
  have f4 := f3.after_registers ready4 e4.agrees (by simp [mulM64Effect, Effect.components, Component.Covers]) (by simp [mulM64Effect, Effect.components])
  have m4 : u4.external = t.external := (e4.agrees.external (by simp [mulM64Effect, Effect.components, Component.Covers])).trans m3
  have load4 : memLoad u3.external (stackPtr u3 + 56) 64 = 0xffffffffffffffff := by
    rw [f3.rsp, m3]
    exact state.slots.p0
  have g4r0 : ((Operand.reg 0 : Operand 64).read u4) = p0.1 := by
    have h := e4.writes.1
    change ((Operand.reg 0 : Operand 64).read u4) = ((Operand.reg 0 : Operand 64).read u3) * (memLoad u3.external (stackPtr u3 + 56) 64) at h
    rw [g3r0, load4] at h
    simpa only [← eq_p0, product64] using h
  have g4r2 : ((Operand.reg 2 : Operand 64).read u4) = p0.2 := by
    have h := e4.writes.2
    change ((Operand.reg 2 : Operand 64).read u4) = mulHigh64 ((Operand.reg 0 : Operand 64).read u3) (memLoad u3.external (stackPtr u3 + 56) 64) at h
    rw [g3r0, load4] at h
    simpa only [← eq_p0, product64] using h
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (mov_r64_r64_effect_step 0x11351f 0x48 0xd1 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x1351f _ (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13522 (by decide)))
  change (movR64R64Effect 0x11351f 1 2 u4).Holds u4 u5 at e5
  have f5 := f4.after_registers ready5 e5.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have m5 : u5.external = t.external := (e5.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans m4
  have g5r1 : ((Operand.reg 1 : Operand 64).read u5) = p0.2 := by
    have h := e5.writes
    change ((Operand.reg 1 : Operand 64).read u5) = ((Operand.reg 2 : Operand 64).read u4) at h
    rw [g4r2] at h
    exact h
  have g5r0 : ((Operand.reg 0 : Operand 64).read u5) = p0.1 := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r0
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (mov_r64_r64_effect_step 0x113522 0x49 0xc0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x13522 _ (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13525 (by decide)))
  change (movR64R64Effect 0x113522 8 0 u5).Holds u5 u6 at e6
  have f6 := f5.after_registers ready6 e6.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have m6 : u6.external = t.external := (e6.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans m5
  have g6r8 : ((Operand.reg 8 : Operand 64).read u6) = p0.1 := by
    have h := e6.writes
    change ((Operand.reg 8 : Operand 64).read u6) = ((Operand.reg 0 : Operand 64).read u5) at h
    rw [g5r0] at h
    exact h
  have g3r11 : ((Operand.reg 11 : Operand 64).read u3) = a := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r11
  have g4r11 : ((Operand.reg 11 : Operand 64).read u4) = a := (e4.agrees.read (by simp [mulM64Effect, Effect.components])).trans g3r11
  have g5r11 : ((Operand.reg 11 : Operand 64).read u5) = a := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r11
  have g6r11 : ((Operand.reg 11 : Operand 64).read u6) = a := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r11
  obtain ⟨u7, run7, ready7, e7⟩ :=
    (mov_r64_r64_effect_step 0x113525 0x4c 0xd8 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x13525 _ (by decide) (by decide +kernel))
      e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13528 (by decide)))
  change (movR64R64Effect 0x113525 0 11 u6).Holds u6 u7 at e7
  have f7 := f6.after_registers ready7 e7.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have m7 : u7.external = t.external := (e7.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans m6
  have g7r0 : ((Operand.reg 0 : Operand 64).read u7) = a := by
    have h := e7.writes
    change ((Operand.reg 0 : Operand 64).read u7) = ((Operand.reg 11 : Operand 64).read u6) at h
    rw [g6r11] at h
    exact h
  obtain ⟨u8, run8, ready8, e8⟩ :=
    (mov_r64_m64_effect_step 0x113528 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x13528 _ (by decide) (by decide +kernel))
      ⟨e7.rip, ScalarFrame.stack_readable pre.toCalleePre f7 (offset := 48) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1352d (by decide)))
  change (movR64M64Effect 0x113528 6 (.sib 4 none 0 (.d8 48)) u7).Holds u7 u8 at e8
  have f8 := f7.after_registers ready8 e8.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have m8 : u8.external = t.external := (e8.agrees.external (by simp [movR64M64Effect_components, Component.Covers])).trans m7
  have load8 : memLoad u7.external (stackPtr u7 + 48) 64 = 0xffffffff := by
    rw [f7.rsp, m7]
    exact state.slots.p1
  have g8r6 : ((Operand.reg 6 : Operand 64).read u8) = 0xffffffff := by
    have h := e8.writes
    change ((Operand.reg 6 : Operand 64).read u8) = memLoad u7.external (stackPtr u7 + 48) 64 at h
    rw [load8] at h
    exact h
  have g8r0 : ((Operand.reg 0 : Operand 64).read u8) = a := (e8.agrees.read (by simp [movR64M64Effect_components])).trans g7r0
  obtain ⟨u9, run9, ready9, e9⟩ :=
    (mul_r64_effect_step 0x11352d 0x48 0xe6 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x1352d _ (by decide) (by decide +kernel))
      e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13530 (by decide)))
  change (mulR64Effect 0x11352d 6 u8).Holds u8 u9 at e9
  have f9 := f8.after_registers ready9 e9.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have m9 : u9.external = t.external := (e9.agrees.external (by simp [mulR64Effect_components, Component.Covers])).trans m8
  have g9r0 : ((Operand.reg 0 : Operand 64).read u9) = p1.1 := by
    have h := e9.writes.1
    change ((Operand.reg 0 : Operand 64).read u9) = ((Operand.reg 0 : Operand 64).read u8) * ((Operand.reg 6 : Operand 64).read u8) at h
    rw [g8r0, g8r6] at h
    simpa only [← eq_p1, product64] using h
  have g9r2 : ((Operand.reg 2 : Operand 64).read u9) = p1.2 := by
    have h := e9.writes.2
    change ((Operand.reg 2 : Operand 64).read u9) = mulHigh64 ((Operand.reg 0 : Operand 64).read u8) ((Operand.reg 6 : Operand 64).read u8) at h
    rw [g8r0, g8r6] at h
    simpa only [← eq_p1, product64] using h
  obtain ⟨u10, run10, ready10, e10⟩ :=
    (mov_r64_r64_effect_step 0x113530 0x49 0xd7 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x13530 _ (by decide) (by decide +kernel))
      e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13533 (by decide)))
  change (movR64R64Effect 0x113530 15 2 u9).Holds u9 u10 at e10
  have f10 := f9.after_registers ready10 e10.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have m10 : u10.external = t.external := (e10.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans m9
  have g10r15 : ((Operand.reg 15 : Operand 64).read u10) = p1.2 := by
    have h := e10.writes
    change ((Operand.reg 15 : Operand 64).read u10) = ((Operand.reg 2 : Operand 64).read u9) at h
    rw [g9r2] at h
    exact h
  have g10r0 : ((Operand.reg 0 : Operand 64).read u10) = p1.1 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r0
  obtain ⟨u11, run11, ready11, e11⟩ :=
    (mov_r64_r64_effect_step 0x113533 0x49 0xc4 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x13533 _ (by decide) (by decide +kernel))
      e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13536 (by decide)))
  change (movR64R64Effect 0x113533 12 0 u10).Holds u10 u11 at e11
  have f11 := f10.after_registers ready11 e11.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have m11 : u11.external = t.external := (e11.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans m10
  have g11r12 : ((Operand.reg 12 : Operand 64).read u11) = p1.1 := by
    have h := e11.writes
    change ((Operand.reg 12 : Operand 64).read u11) = ((Operand.reg 0 : Operand 64).read u10) at h
    rw [g10r0] at h
    exact h
  have g1r5 : ((Operand.reg 5 : Operand 64).read u1) = b := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r5
  have g2r5 : ((Operand.reg 5 : Operand 64).read u2) = b := (e2.agrees.read (by simp [FirstRound.imulR64R64Effect_components])).trans g1r5
  have g3r5 : ((Operand.reg 5 : Operand 64).read u3) = b := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r5
  have g4r5 : ((Operand.reg 5 : Operand 64).read u4) = b := (e4.agrees.read (by simp [mulM64Effect, Effect.components])).trans g3r5
  have g5r5 : ((Operand.reg 5 : Operand 64).read u5) = b := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r5
  have g6r5 : ((Operand.reg 5 : Operand 64).read u6) = b := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r5
  have g7r5 : ((Operand.reg 5 : Operand 64).read u7) = b := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r5
  have g8r5 : ((Operand.reg 5 : Operand 64).read u8) = b := (e8.agrees.read (by simp [movR64M64Effect_components])).trans g7r5
  have g9r5 : ((Operand.reg 5 : Operand 64).read u9) = b := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r5
  have g10r5 : ((Operand.reg 5 : Operand 64).read u10) = b := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r5
  have g11r5 : ((Operand.reg 5 : Operand 64).read u11) = b := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r5
  obtain ⟨u12, run12, ready12, e12⟩ :=
    (add_r64_r64_effect_step 0x113536 0x49 0xec (by simp [RexWPrefix]) (by decide)).advances (readyToStep f11.machine f11.bindingsSupported)
      (programText_slice (programLoaded_codeIn f11.loaded) 0x13536 _ (by decide) (by decide +kernel))
      e11.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13539 (by decide)))
  change (addR64R64Effect 0x113536 12 5 u11).Holds u11 u12 at e12
  have f12 := f11.after_registers ready12 e12.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have m12 : u12.external = t.external := (e12.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans m11
  have g12r12 : ((Operand.reg 12 : Operand 64).read u12) = x.1 := by
    have h := e12.writes
    change ((Operand.reg 12 : Operand 64).read u12) = (addSpec ((Operand.reg 12 : Operand 64).read u11) ((Operand.reg 5 : Operand 64).read u11)).1 at h
    rw [g11r5, g11r12] at h
    simpa only [← eq_x, add64] using h
  have cf12 : (StatusFlags.ofRFLAGS u12.RFLAGS).CF = x.2 := by
    have h := e12.flags.1
    change (StatusFlags.ofRFLAGS u12.RFLAGS).CF = (addSpec ((Operand.reg 12 : Operand 64).read u11) ((Operand.reg 5 : Operand 64).read u11)).2.CF at h
    rw [g11r5, g11r12] at h
    simpa only [← eq_x, add64] using h
  have g11r15 : ((Operand.reg 15 : Operand 64).read u11) = p1.2 := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r15
  have g12r15 : ((Operand.reg 15 : Operand 64).read u12) = p1.2 := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r15
  obtain ⟨u13, run13, ready13, e13⟩ :=
    (adc_r64_imm8_effect_step 0x113539 0x49 0xd7 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f12.machine f12.bindingsSupported)
      (programText_slice (programLoaded_codeIn f12.loaded) 0x13539 _ (by decide) (by decide +kernel))
      e12.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1353d (by decide)))
  change (adcR64Imm8Effect 0x113539 15 0 u12).Holds u12 u13 at e13
  have f13 := f12.after_registers ready13 e13.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have m13 : u13.external = t.external := (e13.agrees.external (by simp [adcR64Imm8Effect_components, Component.Covers])).trans m12
  have g13r15 : ((Operand.reg 15 : Operand 64).read u13) = h.1 := by
    have h := e13.writes
    change ((Operand.reg 15 : Operand 64).read u13) = (adcSpec ((Operand.reg 15 : Operand 64).read u12) 0 (u12.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g12r15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf12] at h
    simpa only [← eq_h, adc64] using h
  have cf13 : (StatusFlags.ofRFLAGS u13.RFLAGS).CF = h.2 := by
    have h := e13.flags.1
    change (StatusFlags.ofRFLAGS u13.RFLAGS).CF = (adcSpec ((Operand.reg 15 : Operand 64).read u12) 0 (u12.RFLAGS.extractLsb' 0 1)).2.CF at h
    rw [g12r15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf12] at h
    simpa only [← eq_h, adc64] using h
  have g2r13 : ((Operand.reg 13 : Operand 64).read u2) = a := (e2.agrees.read (by simp [FirstRound.imulR64R64Effect_components])).trans g1r13
  have g3r13 : ((Operand.reg 13 : Operand 64).read u3) = a := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r13
  have g4r13 : ((Operand.reg 13 : Operand 64).read u4) = a := (e4.agrees.read (by simp [mulM64Effect, Effect.components])).trans g3r13
  have g5r13 : ((Operand.reg 13 : Operand 64).read u5) = a := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r13
  have g6r13 : ((Operand.reg 13 : Operand 64).read u6) = a := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r13
  have g7r13 : ((Operand.reg 13 : Operand 64).read u7) = a := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r13
  have g8r13 : ((Operand.reg 13 : Operand 64).read u8) = a := (e8.agrees.read (by simp [movR64M64Effect_components])).trans g7r13
  have g9r13 : ((Operand.reg 13 : Operand 64).read u9) = a := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r13
  have g10r13 : ((Operand.reg 13 : Operand 64).read u10) = a := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r13
  have g11r13 : ((Operand.reg 13 : Operand 64).read u11) = a := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r13
  have g12r13 : ((Operand.reg 13 : Operand 64).read u12) = a := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r13
  have g13r13 : ((Operand.reg 13 : Operand 64).read u13) = a := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r13
  have g7r8 : ((Operand.reg 8 : Operand 64).read u7) = p0.1 := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r8
  have g8r8 : ((Operand.reg 8 : Operand 64).read u8) = p0.1 := (e8.agrees.read (by simp [movR64M64Effect_components])).trans g7r8
  have g9r8 : ((Operand.reg 8 : Operand 64).read u9) = p0.1 := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r8
  have g10r8 : ((Operand.reg 8 : Operand 64).read u10) = p0.1 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r8
  have g11r8 : ((Operand.reg 8 : Operand 64).read u11) = p0.1 := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r8
  have g12r8 : ((Operand.reg 8 : Operand 64).read u12) = p0.1 := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r8
  have g13r8 : ((Operand.reg 8 : Operand 64).read u13) = p0.1 := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r8
  obtain ⟨u14, run14, ready14, e14⟩ :=
    (add_r64_r64_effect_step 0x11353d 0x4d 0xe8 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f13.machine f13.bindingsSupported)
      (programText_slice (programLoaded_codeIn f13.loaded) 0x1353d _ (by decide) (by decide +kernel))
      e13.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13540 (by decide)))
  change (addR64R64Effect 0x11353d 8 13 u13).Holds u13 u14 at e14
  have f14 := f13.after_registers ready14 e14.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have m14 : u14.external = t.external := (e14.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans m13
  have g14r8 : ((Operand.reg 8 : Operand 64).read u14) = z.1 := by
    have h := e14.writes
    change ((Operand.reg 8 : Operand 64).read u14) = (addSpec ((Operand.reg 8 : Operand 64).read u13) ((Operand.reg 13 : Operand 64).read u13)).1 at h
    rw [g13r13, g13r8] at h
    simpa only [← eq_z, add64] using h
  have cf14 : (StatusFlags.ofRFLAGS u14.RFLAGS).CF = z.2 := by
    have h := e14.flags.1
    change (StatusFlags.ofRFLAGS u14.RFLAGS).CF = (addSpec ((Operand.reg 8 : Operand 64).read u13) ((Operand.reg 13 : Operand 64).read u13)).2.CF at h
    rw [g13r13, g13r8] at h
    simpa only [← eq_z, add64] using h
  have g6r1 : ((Operand.reg 1 : Operand 64).read u6) = p0.2 := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r1
  have g7r1 : ((Operand.reg 1 : Operand 64).read u7) = p0.2 := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r1
  have g8r1 : ((Operand.reg 1 : Operand 64).read u8) = p0.2 := (e8.agrees.read (by simp [movR64M64Effect_components])).trans g7r1
  have g9r1 : ((Operand.reg 1 : Operand 64).read u9) = p0.2 := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r1
  have g10r1 : ((Operand.reg 1 : Operand 64).read u10) = p0.2 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r1
  have g11r1 : ((Operand.reg 1 : Operand 64).read u11) = p0.2 := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r1
  have g12r1 : ((Operand.reg 1 : Operand 64).read u12) = p0.2 := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r1
  have g13r1 : ((Operand.reg 1 : Operand 64).read u13) = p0.2 := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r1
  have g14r1 : ((Operand.reg 1 : Operand 64).read u14) = p0.2 := (e14.agrees.read (by simp [addR64R64Effect_components])).trans g13r1
  have g13r12 : ((Operand.reg 12 : Operand 64).read u13) = x.1 := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r12
  have g14r12 : ((Operand.reg 12 : Operand 64).read u14) = x.1 := (e14.agrees.read (by simp [addR64R64Effect_components])).trans g13r12
  obtain ⟨u15, run15, ready15, e15⟩ :=
    (adc_r64_r64_effect_step 0x113540 0x49 0xcc (by simp [RexWPrefix]) (by decide)).advances (readyToStep f14.machine f14.bindingsSupported)
      (programText_slice (programLoaded_codeIn f14.loaded) 0x13540 _ (by decide) (by decide +kernel))
      e14.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13543 (by decide)))
  change (adcR64R64Effect 0x113540 12 1 u14).Holds u14 u15 at e15
  have f15 := f14.after_registers ready15 e15.agrees (by simp [adcR64R64Effect_components, Component.Covers]) (by simp [adcR64R64Effect_components])
  have m15 : u15.external = t.external := (e15.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans m14
  have g15r12 : ((Operand.reg 12 : Operand 64).read u15) = y.1 := by
    have h := e15.writes
    change ((Operand.reg 12 : Operand 64).read u15) = (adcSpec ((Operand.reg 12 : Operand 64).read u14) ((Operand.reg 1 : Operand 64).read u14) (u14.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g14r1, g14r12, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf14] at h
    simpa only [← eq_y, adc64] using h
  have cf15 : (StatusFlags.ofRFLAGS u15.RFLAGS).CF = y.2 := by
    have h := e15.flags.1
    change (StatusFlags.ofRFLAGS u15.RFLAGS).CF = (adcSpec ((Operand.reg 12 : Operand 64).read u14) ((Operand.reg 1 : Operand 64).read u14) (u14.RFLAGS.extractLsb' 0 1)).2.CF at h
    rw [g14r1, g14r12, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf14] at h
    simpa only [← eq_y, adc64] using h
  have g14r15 : ((Operand.reg 15 : Operand 64).read u14) = h.1 := (e14.agrees.read (by simp [addR64R64Effect_components])).trans g13r15
  have g15r15 : ((Operand.reg 15 : Operand 64).read u15) = h.1 := (e15.agrees.read (by simp [adcR64R64Effect_components])).trans g14r15
  obtain ⟨u16, run16, ready16, e16⟩ :=
    (adc_r64_imm8_effect_step 0x113543 0x49 0xd7 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f15.machine f15.bindingsSupported)
      (programText_slice (programLoaded_codeIn f15.loaded) 0x13543 _ (by decide) (by decide +kernel))
      e15.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13547 (by decide)))
  change (adcR64Imm8Effect 0x113543 15 0 u15).Holds u15 u16 at e16
  have f16 := f15.after_registers ready16 e16.agrees (by simp [adcR64Imm8Effect_components, Component.Covers]) (by simp [adcR64Imm8Effect_components])
  have m16 : u16.external = t.external := (e16.agrees.external (by simp [adcR64Imm8Effect_components, Component.Covers])).trans m15
  have g16r15 : ((Operand.reg 15 : Operand 64).read u16) = k.1 := by
    have h := e16.writes
    change ((Operand.reg 15 : Operand 64).read u16) = (adcSpec ((Operand.reg 15 : Operand 64).read u15) 0 (u15.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g15r15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf15] at h
    simpa only [← eq_k, adc64] using h
  have cf16 : (StatusFlags.ofRFLAGS u16.RFLAGS).CF = k.2 := by
    have h := e16.flags.1
    change (StatusFlags.ofRFLAGS u16.RFLAGS).CF = (adcSpec ((Operand.reg 15 : Operand 64).read u15) 0 (u15.RFLAGS.extractLsb' 0 1)).2.CF at h
    rw [g15r15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf15] at h
    simpa only [← eq_k, adc64] using h
  have g1r10 : ((Operand.reg 10 : Operand 64).read u1) = 0 := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r10
  have g2r10 : ((Operand.reg 10 : Operand 64).read u2) = 0 := (e2.agrees.read (by simp [FirstRound.imulR64R64Effect_components])).trans g1r10
  have g3r10 : ((Operand.reg 10 : Operand 64).read u3) = 0 := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r10
  have g4r10 : ((Operand.reg 10 : Operand 64).read u4) = 0 := (e4.agrees.read (by simp [mulM64Effect, Effect.components])).trans g3r10
  have g5r10 : ((Operand.reg 10 : Operand 64).read u5) = 0 := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r10
  have g6r10 : ((Operand.reg 10 : Operand 64).read u6) = 0 := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r10
  have g7r10 : ((Operand.reg 10 : Operand 64).read u7) = 0 := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r10
  have g8r10 : ((Operand.reg 10 : Operand 64).read u8) = 0 := (e8.agrees.read (by simp [movR64M64Effect_components])).trans g7r10
  have g9r10 : ((Operand.reg 10 : Operand 64).read u9) = 0 := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r10
  have g10r10 : ((Operand.reg 10 : Operand 64).read u10) = 0 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r10
  have g11r10 : ((Operand.reg 10 : Operand 64).read u11) = 0 := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r10
  have g12r10 : ((Operand.reg 10 : Operand 64).read u12) = 0 := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r10
  have g13r10 : ((Operand.reg 10 : Operand 64).read u13) = 0 := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r10
  have g14r10 : ((Operand.reg 10 : Operand 64).read u14) = 0 := (e14.agrees.read (by simp [addR64R64Effect_components])).trans g13r10
  have g15r10 : ((Operand.reg 10 : Operand 64).read u15) = 0 := (e15.agrees.read (by simp [adcR64R64Effect_components])).trans g14r10
  have g16r10 : ((Operand.reg 10 : Operand 64).read u16) = 0 := (e16.agrees.read (by simp [adcR64Imm8Effect_components])).trans g15r10
  obtain ⟨u17, run17, ready17, e17⟩ :=
    (mov_r64_r64_effect_step 0x113547 0x4c 0xd0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f16.machine f16.bindingsSupported)
      (programText_slice (programLoaded_codeIn f16.loaded) 0x13547 _ (by decide) (by decide +kernel))
      e16.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1354a (by decide)))
  change (movR64R64Effect 0x113547 0 10 u16).Holds u16 u17 at e17
  have f17 := f16.after_registers ready17 e17.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have m17 : u17.external = t.external := (e17.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans m16
  have g17r0 : ((Operand.reg 0 : Operand 64).read u17) = 0 := by
    have h := e17.writes
    change ((Operand.reg 0 : Operand 64).read u17) = ((Operand.reg 10 : Operand 64).read u16) at h
    rw [g16r10] at h
    exact h
  have g7r11 : ((Operand.reg 11 : Operand 64).read u7) = a := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r11
  have g8r11 : ((Operand.reg 11 : Operand 64).read u8) = a := (e8.agrees.read (by simp [movR64M64Effect_components])).trans g7r11
  have g9r11 : ((Operand.reg 11 : Operand 64).read u9) = a := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r11
  have g10r11 : ((Operand.reg 11 : Operand 64).read u10) = a := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r11
  have g11r11 : ((Operand.reg 11 : Operand 64).read u11) = a := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r11
  have g12r11 : ((Operand.reg 11 : Operand 64).read u12) = a := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r11
  have g13r11 : ((Operand.reg 11 : Operand 64).read u13) = a := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r11
  have g14r11 : ((Operand.reg 11 : Operand 64).read u14) = a := (e14.agrees.read (by simp [addR64R64Effect_components])).trans g13r11
  have g15r11 : ((Operand.reg 11 : Operand 64).read u15) = a := (e15.agrees.read (by simp [adcR64R64Effect_components])).trans g14r11
  have g16r11 : ((Operand.reg 11 : Operand 64).read u16) = a := (e16.agrees.read (by simp [adcR64Imm8Effect_components])).trans g15r11
  have g17r11 : ((Operand.reg 11 : Operand 64).read u17) = a := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r11
  obtain ⟨u18, run18, ready18, e18⟩ :=
    (mul_r64_effect_step 0x11354a 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f17.machine f17.bindingsSupported)
      (programText_slice (programLoaded_codeIn f17.loaded) 0x1354a _ (by decide) (by decide +kernel))
      e17.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1354d (by decide)))
  change (mulR64Effect 0x11354a 11 u17).Holds u17 u18 at e18
  have f18 := f17.after_registers ready18 e18.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have m18 : u18.external = t.external := (e18.agrees.external (by simp [mulR64Effect_components, Component.Covers])).trans m17
  have g18r0 : ((Operand.reg 0 : Operand 64).read u18) = 0 := by
    have h := e18.writes.1
    change ((Operand.reg 0 : Operand 64).read u18) = ((Operand.reg 0 : Operand 64).read u17) * ((Operand.reg 11 : Operand 64).read u17) at h
    rw [g17r0, g17r11] at h
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.zero_mul] using h
  have g18r2 : ((Operand.reg 2 : Operand 64).read u18) = 0 := by
    have h := e18.writes.2
    change ((Operand.reg 2 : Operand 64).read u18) = mulHigh64 ((Operand.reg 0 : Operand 64).read u17) ((Operand.reg 11 : Operand 64).read u17) at h
    rw [g17r0, g17r11] at h
    simpa only [mulHigh64, BitVec.ofNat_eq_ofNat, BitVec.toNat_zero, Nat.zero_mul, Nat.zero_div] using h
  have g16r12 : ((Operand.reg 12 : Operand 64).read u16) = y.1 := (e16.agrees.read (by simp [adcR64Imm8Effect_components])).trans g15r12
  have g17r12 : ((Operand.reg 12 : Operand 64).read u17) = y.1 := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r12
  have g18r12 : ((Operand.reg 12 : Operand 64).read u18) = y.1 := (e18.agrees.read (by simp [mulR64Effect_components])).trans g17r12
  have g17r15 : ((Operand.reg 15 : Operand 64).read u17) = k.1 := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r15
  have g18r15 : ((Operand.reg 15 : Operand 64).read u18) = k.1 := (e18.agrees.read (by simp [mulR64Effect_components])).trans g17r15
  have g18r11 : ((Operand.reg 11 : Operand 64).read u18) = a := (e18.agrees.read (by simp [mulR64Effect_components])).trans g17r11
  have g1r3 : ((Operand.reg 3 : Operand 64).read u1) = c := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r3
  have g2r3 : ((Operand.reg 3 : Operand 64).read u2) = c := (e2.agrees.read (by simp [FirstRound.imulR64R64Effect_components])).trans g1r3
  have g3r3 : ((Operand.reg 3 : Operand 64).read u3) = c := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r3
  have g4r3 : ((Operand.reg 3 : Operand 64).read u4) = c := (e4.agrees.read (by simp [mulM64Effect, Effect.components])).trans g3r3
  have g5r3 : ((Operand.reg 3 : Operand 64).read u5) = c := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r3
  have g6r3 : ((Operand.reg 3 : Operand 64).read u6) = c := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r3
  have g7r3 : ((Operand.reg 3 : Operand 64).read u7) = c := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r3
  have g8r3 : ((Operand.reg 3 : Operand 64).read u8) = c := (e8.agrees.read (by simp [movR64M64Effect_components])).trans g7r3
  have g9r3 : ((Operand.reg 3 : Operand 64).read u9) = c := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r3
  have g10r3 : ((Operand.reg 3 : Operand 64).read u10) = c := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r3
  have g11r3 : ((Operand.reg 3 : Operand 64).read u11) = c := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r3
  have g12r3 : ((Operand.reg 3 : Operand 64).read u12) = c := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r3
  have g13r3 : ((Operand.reg 3 : Operand 64).read u13) = c := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r3
  have g14r3 : ((Operand.reg 3 : Operand 64).read u14) = c := (e14.agrees.read (by simp [addR64R64Effect_components])).trans g13r3
  have g15r3 : ((Operand.reg 3 : Operand 64).read u15) = c := (e15.agrees.read (by simp [adcR64R64Effect_components])).trans g14r3
  have g16r3 : ((Operand.reg 3 : Operand 64).read u16) = c := (e16.agrees.read (by simp [adcR64Imm8Effect_components])).trans g15r3
  have g17r3 : ((Operand.reg 3 : Operand 64).read u17) = c := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r3
  have g18r3 : ((Operand.reg 3 : Operand 64).read u18) = c := (e18.agrees.read (by simp [mulR64Effect_components])).trans g17r3
  have g1r14 : ((Operand.reg 14 : Operand 64).read u1) = d := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r14
  have g2r14 : ((Operand.reg 14 : Operand 64).read u2) = d := (e2.agrees.read (by simp [FirstRound.imulR64R64Effect_components])).trans g1r14
  have g3r14 : ((Operand.reg 14 : Operand 64).read u3) = d := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r14
  have g4r14 : ((Operand.reg 14 : Operand 64).read u4) = d := (e4.agrees.read (by simp [mulM64Effect, Effect.components])).trans g3r14
  have g5r14 : ((Operand.reg 14 : Operand 64).read u5) = d := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r14
  have g6r14 : ((Operand.reg 14 : Operand 64).read u6) = d := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r14
  have g7r14 : ((Operand.reg 14 : Operand 64).read u7) = d := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r14
  have g8r14 : ((Operand.reg 14 : Operand 64).read u8) = d := (e8.agrees.read (by simp [movR64M64Effect_components])).trans g7r14
  have g9r14 : ((Operand.reg 14 : Operand 64).read u9) = d := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r14
  have g10r14 : ((Operand.reg 14 : Operand 64).read u10) = d := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r14
  have g11r14 : ((Operand.reg 14 : Operand 64).read u11) = d := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r14
  have g12r14 : ((Operand.reg 14 : Operand 64).read u12) = d := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r14
  have g13r14 : ((Operand.reg 14 : Operand 64).read u13) = d := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r14
  have g14r14 : ((Operand.reg 14 : Operand 64).read u14) = d := (e14.agrees.read (by simp [addR64R64Effect_components])).trans g13r14
  have g15r14 : ((Operand.reg 14 : Operand 64).read u15) = d := (e15.agrees.read (by simp [adcR64R64Effect_components])).trans g14r14
  have g16r14 : ((Operand.reg 14 : Operand 64).read u16) = d := (e16.agrees.read (by simp [adcR64Imm8Effect_components])).trans g15r14
  have g17r14 : ((Operand.reg 14 : Operand 64).read u17) = d := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r14
  have g18r14 : ((Operand.reg 14 : Operand 64).read u18) = d := (e18.agrees.read (by simp [mulR64Effect_components])).trans g17r14
  have g1r9 : ((Operand.reg 9 : Operand 64).read u1) = extra := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r9
  have g2r9 : ((Operand.reg 9 : Operand 64).read u2) = extra := (e2.agrees.read (by simp [FirstRound.imulR64R64Effect_components])).trans g1r9
  have g3r9 : ((Operand.reg 9 : Operand 64).read u3) = extra := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r9
  have g4r9 : ((Operand.reg 9 : Operand 64).read u4) = extra := (e4.agrees.read (by simp [mulM64Effect, Effect.components])).trans g3r9
  have g5r9 : ((Operand.reg 9 : Operand 64).read u5) = extra := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r9
  have g6r9 : ((Operand.reg 9 : Operand 64).read u6) = extra := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r9
  have g7r9 : ((Operand.reg 9 : Operand 64).read u7) = extra := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r9
  have g8r9 : ((Operand.reg 9 : Operand 64).read u8) = extra := (e8.agrees.read (by simp [movR64M64Effect_components])).trans g7r9
  have g9r9 : ((Operand.reg 9 : Operand 64).read u9) = extra := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r9
  have g10r9 : ((Operand.reg 9 : Operand 64).read u10) = extra := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r9
  have g11r9 : ((Operand.reg 9 : Operand 64).read u11) = extra := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r9
  have g12r9 : ((Operand.reg 9 : Operand 64).read u12) = extra := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r9
  have g13r9 : ((Operand.reg 9 : Operand 64).read u13) = extra := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r9
  have g14r9 : ((Operand.reg 9 : Operand 64).read u14) = extra := (e14.agrees.read (by simp [addR64R64Effect_components])).trans g13r9
  have g15r9 : ((Operand.reg 9 : Operand 64).read u15) = extra := (e15.agrees.read (by simp [adcR64R64Effect_components])).trans g14r9
  have g16r9 : ((Operand.reg 9 : Operand 64).read u16) = extra := (e16.agrees.read (by simp [adcR64Imm8Effect_components])).trans g15r9
  have g17r9 : ((Operand.reg 9 : Operand 64).read u17) = extra := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r9
  have g18r9 : ((Operand.reg 9 : Operand 64).read u18) = extra := (e18.agrees.read (by simp [mulR64Effect_components])).trans g17r9
  have g1r7 : ((Operand.reg 7 : Operand 64).read u1) = s.regValue .rdi := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r7
  have g2r7 : ((Operand.reg 7 : Operand 64).read u2) = s.regValue .rdi := (e2.agrees.read (by simp [FirstRound.imulR64R64Effect_components])).trans g1r7
  have g3r7 : ((Operand.reg 7 : Operand 64).read u3) = s.regValue .rdi := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r7
  have g4r7 : ((Operand.reg 7 : Operand 64).read u4) = s.regValue .rdi := (e4.agrees.read (by simp [mulM64Effect, Effect.components])).trans g3r7
  have g5r7 : ((Operand.reg 7 : Operand 64).read u5) = s.regValue .rdi := (e5.agrees.read (by simp [movR64R64Effect_components])).trans g4r7
  have g6r7 : ((Operand.reg 7 : Operand 64).read u6) = s.regValue .rdi := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r7
  have g7r7 : ((Operand.reg 7 : Operand 64).read u7) = s.regValue .rdi := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r7
  have g8r7 : ((Operand.reg 7 : Operand 64).read u8) = s.regValue .rdi := (e8.agrees.read (by simp [movR64M64Effect_components])).trans g7r7
  have g9r7 : ((Operand.reg 7 : Operand 64).read u9) = s.regValue .rdi := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r7
  have g10r7 : ((Operand.reg 7 : Operand 64).read u10) = s.regValue .rdi := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r7
  have g11r7 : ((Operand.reg 7 : Operand 64).read u11) = s.regValue .rdi := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r7
  have g12r7 : ((Operand.reg 7 : Operand 64).read u12) = s.regValue .rdi := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r7
  have g13r7 : ((Operand.reg 7 : Operand 64).read u13) = s.regValue .rdi := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r7
  have g14r7 : ((Operand.reg 7 : Operand 64).read u14) = s.regValue .rdi := (e14.agrees.read (by simp [addR64R64Effect_components])).trans g13r7
  have g15r7 : ((Operand.reg 7 : Operand 64).read u15) = s.regValue .rdi := (e15.agrees.read (by simp [adcR64R64Effect_components])).trans g14r7
  have g16r7 : ((Operand.reg 7 : Operand 64).read u16) = s.regValue .rdi := (e16.agrees.read (by simp [adcR64Imm8Effect_components])).trans g15r7
  have g17r7 : ((Operand.reg 7 : Operand 64).read u17) = s.regValue .rdi := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r7
  have g18r7 : ((Operand.reg 7 : Operand 64).read u18) = s.regValue .rdi := (e18.agrees.read (by simp [mulR64Effect_components])).trans g17r7
  have g9r6 : ((Operand.reg 6 : Operand 64).read u9) = 0xffffffff := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r6
  have g10r6 : ((Operand.reg 6 : Operand 64).read u10) = 0xffffffff := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r6
  have g11r6 : ((Operand.reg 6 : Operand 64).read u11) = 0xffffffff := (e11.agrees.read (by simp [movR64R64Effect_components])).trans g10r6
  have g12r6 : ((Operand.reg 6 : Operand 64).read u12) = 0xffffffff := (e12.agrees.read (by simp [addR64R64Effect_components])).trans g11r6
  have g13r6 : ((Operand.reg 6 : Operand 64).read u13) = 0xffffffff := (e13.agrees.read (by simp [adcR64Imm8Effect_components])).trans g12r6
  have g14r6 : ((Operand.reg 6 : Operand 64).read u14) = 0xffffffff := (e14.agrees.read (by simp [addR64R64Effect_components])).trans g13r6
  have g15r6 : ((Operand.reg 6 : Operand 64).read u15) = 0xffffffff := (e15.agrees.read (by simp [adcR64R64Effect_components])).trans g14r6
  have g16r6 : ((Operand.reg 6 : Operand 64).read u16) = 0xffffffff := (e16.agrees.read (by simp [adcR64Imm8Effect_components])).trans g15r6
  have g17r6 : ((Operand.reg 6 : Operand 64).read u17) = 0xffffffff := (e17.agrees.read (by simp [movR64R64Effect_components])).trans g16r6
  have g18r6 : ((Operand.reg 6 : Operand 64).read u18) = 0xffffffff := (e18.agrees.read (by simp [mulR64Effect_components])).trans g17r6
  have lowWords : thirdLow a b = (y.1, k.1) := by
    simp only [thirdLow, eq_p0, eq_p1, eq_x, eq_h, eq_z, eq_y, eq_k]
  exact ⟨u18, ⟨18, (((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17).trans run18)⟩, ⟨f18, e18.rip, m18, (by change ((Operand.reg 12 : Operand 64).read u18) = (thirdLow a b).1; rw [lowWords]; exact g18r12), (by change ((Operand.reg 15 : Operand 64).read u18) = (thirdLow a b).2; rw [lowWords]; exact g18r15), g18r11, g18r0, g18r2, g18r3, g18r14, g18r9, g18r7, g18r6⟩⟩


end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper
