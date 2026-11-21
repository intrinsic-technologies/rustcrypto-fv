import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Stages
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.First.Support
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.FourthArithmetic
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Instructions.Setb.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.FourthRound

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Common.Instructions.CrossPageStore
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Instructions.MovzxByte
open P256.Proofs.Field.Montgomery (add64 adc64 product64)
open FirstRound (after_store input_readable imulR64R64Effect_components)

theorem movzxR32R8Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (movzxR32R8Effect p len dst src s).components = [.reg dst, .rip] := rfl

theorem bool_byte (b : Bool) : ((if b then 1 else 0 : BitVec 8).setWidth 64) =
    BitVec.ofNat 64 b.toNat := by cases b <;> rfl

theorem bool_merge (b : Bool) : mergeGPR 8 (if b then 1 else 0) 0 =
    BitVec.ofNat 64 b.toNat := by cases b <;> decide +kernel

abbrev inputWords (t : RamState) : Limbs :=
  ⟨t.regValue .r12, t.regValue .r15, t.regValue .r13, t.regValue .r9⟩

structure Output [Bindings] (s t u : RamState) (v : Nat) : Prop where
  frame : ScalarFrame.FrameState s u 32 112 112
  rip : u.RIP = 0x113627
  slots : ModulusSlots s u
  rdi : u.regValue .rdi = s.regValue .rdi
  r11 : u.regValue .r11 = 0xffffffffffffffff
  top : (u.regValue .rdx).toNat + (slot s u 24).toNat +
    2^64 * (slot s u 16).toNat =
      (u.regValue .rax).toNat + 2^64 * (u.regValue .r12).toNat
  words : (⟨u.regValue .rbx, u.regValue .rcx, u.regValue .r8, u.regValue .rax⟩ : Limbs) =
    (fourthWords (inputWords t) (BitVec.ofNat 64 (v / 2^384))
      ((carryByte s t).setWidth 64) (BitVec.ofNat 64 (v / 2^448))).1
  high : u.regValue .r12 =
    (fourthWords (inputWords t) (BitVec.ofNat 64 (v / 2^384))
      ((carryByte s t).setWidth 64) (BitVec.ofNat 64 (v / 2^448))).2

theorem adc_zero_false_word (a : BitVec 64) :
    (adcSpec a 0 (BitVec.ofBool false)).1 = a := by
  simp [adcSpec]

attribute [local irreducible] add64 adc64 product64

set_option exponentiation.threshold 512 in
set_option maxHeartbeats 1800000 in
theorem lower [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : Third s t v)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256))) :
    ∃ u, Advances boundary 21 t u ∧ ScalarFrame.FrameState s u 32 112 112 ∧
      u.RIP = 0x1135d6 ∧ u.external = t.external ∧
      u.regValue .rdi = s.regValue .rdi ∧ u.regValue .r11 = 0xffffffffffffffff ∧
      u.regValue .rsi = s.regValue .rsi ∧ u.regValue .rbp = 0xffffffff00000001 ∧
      u.regValue .rcx = (fourthLow (inputWords t).l0 (inputWords t).l1).2 ∧
      u.regValue .r9 = t.regValue .r9 ∧ u.regValue .r10 = t.regValue .r12 ∧
      u.regValue .r13 = t.regValue .r13 ∧ u.regValue .r14 = BitVec.ofNat 64 (v / 2^384) ∧
      u.regValue .rax = 0 ∧ u.regValue .rdx = 0 ∧ u.regValue .r8 = 0 ∧ u.regValue .rbx = (fourthLow (inputWords t).l0 (inputWords t).l1).1 := by
  let a := inputWords t
  let extra := BitVec.ofNat 64 (v / 2^384)
  let p0 := product64 a.l0 0xffffffffffffffff
  let p1 := product64 0xffffffff a.l0
  let z := add64 p0.1 a.l0
  let y := adc64 p0.2 a.l1 z.2
  let x := add64 y.1 p1.1
  let k := adc64 (BitVec.ofNat 64 y.2.toNat) p1.2 x.2
  have f0 := state.frame
  have ip0 := state.rip
  have g0r5 : ((Operand.reg 5 : Operand 64).read t) = 0xffffffff00000001 := state.rbp
  have g0r6 : ((Operand.reg 6 : Operand 64).read t) = 0xffffffff := state.rsi
  have g0r7 : ((Operand.reg 7 : Operand 64).read t) = s.regValue .rdi := state.rdi
  have g0r9 : ((Operand.reg 9 : Operand 64).read t) = a.l3 := rfl
  have g0r12 : ((Operand.reg 12 : Operand 64).read t) = a.l0 := rfl
  have g0r13 : ((Operand.reg 13 : Operand 64).read t) = a.l2 := rfl
  have g0r15 : ((Operand.reg 15 : Operand 64).read t) = a.l1 := rfl
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_r64_m64_effect_step 0x11358d 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x1358d _ (by decide) (by decide +kernel))
      ⟨ip0, ScalarFrame.stack_readable pre.toCalleePre f0 (offset := 16) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13592 (by decide)))
  change (movR64M64Effect 0x11358d 8 (.sib 4 none 0 (.d8 16)) t).Holds t u1 at e1
  have f1 := f0.after_registers ready1 e1.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have mem1 : u1.external = t.external := (e1.agrees.external (by simp [movR64M64Effect_components, Component.Covers])).trans rfl
  have load1 : memLoad t.external (((Operand.reg 4 : Operand 64).read t) + 16) 64 = 1 := by
    change memLoad t.external (stackPtr t + 16) 64 = _
    rw [f0.rsp]
    exact state.inverse
  have g1r8 : ((Operand.reg 8 : Operand 64).read u1) = 1 := by
    have h := e1.writes
    change ((Operand.reg 8 : Operand 64).read u1) = memLoad t.external (((Operand.reg 4 : Operand 64).read t) + 16) 64 at h
    rw [load1] at h
    exact h
  have g1r12 : ((Operand.reg 12 : Operand 64).read u1) = a.l0 := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r12
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (imul_r64_r64_effect_step 0x113592 0x4d 0xc4 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x13592 _ (by decide) (by decide +kernel))
      e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13596 (by decide)))
  change (imulR64R64Effect 0x113592 8 12 u1).Holds u1 u2 at e2
  have f2 := f1.after_registers ready2 e2.agrees (by simp [imulR64R64Effect_components, Component.Covers]) (by simp [imulR64R64Effect_components])
  have mem2 : u2.external = t.external := (e2.agrees.external (by simp [imulR64R64Effect_components, Component.Covers])).trans mem1
  have g2r8 : ((Operand.reg 8 : Operand 64).read u2) = a.l0 := by
    have h := e2.writes
    change ((Operand.reg 8 : Operand 64).read u2) = ((Operand.reg 8 : Operand 64).read u1) * ((Operand.reg 12 : Operand 64).read u1) at h
    rw [g1r12, g1r8] at h
    simpa using h
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (mov_r64_r64_effect_step 0x113596 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x13596 _ (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13599 (by decide)))
  change (movR64R64Effect 0x113596 0 8 u2).Holds u2 u3 at e3
  have f3 := f2.after_registers ready3 e3.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have mem3 : u3.external = t.external := (e3.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem2
  have g3r0 : ((Operand.reg 0 : Operand 64).read u3) = a.l0 := by
    have h := e3.writes
    change ((Operand.reg 0 : Operand 64).read u3) = ((Operand.reg 8 : Operand 64).read u2) at h
    rw [g2r8] at h
    exact h
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (mov_r64_m64_effect_step 0x113599 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x13599 _ (by decide) (by decide +kernel))
      ⟨e3.rip, ScalarFrame.stack_readable pre.toCalleePre f3 (offset := 56) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1359e (by decide)))
  change (movR64M64Effect 0x113599 11 (.sib 4 none 0 (.d8 56)) u3).Holds u3 u4 at e4
  have f4 := f3.after_registers ready4 e4.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have mem4 : u4.external = t.external := (e4.agrees.external (by simp [movR64M64Effect_components, Component.Covers])).trans mem3
  have load4 : memLoad u3.external (((Operand.reg 4 : Operand 64).read u3) + 56) 64 = 0xffffffffffffffff := by
    change memLoad u3.external (stackPtr u3 + 56) 64 = _
    rw [f3.rsp, mem3]
    exact state.slots.p0
  have g4r11 : ((Operand.reg 11 : Operand 64).read u4) = 0xffffffffffffffff := by
    have h := e4.writes
    change ((Operand.reg 11 : Operand 64).read u4) = memLoad u3.external (((Operand.reg 4 : Operand 64).read u3) + 56) 64 at h
    rw [load4] at h
    exact h
  have g4r0 : ((Operand.reg 0 : Operand 64).read u4) = a.l0 := (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r0
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (mul_r64_effect_step 0x11359e 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x1359e _ (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135a1 (by decide)))
  change (mulR64Effect 0x11359e 11 u4).Holds u4 u5 at e5
  have f5 := f4.after_registers ready5 e5.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have mem5 : u5.external = t.external := (e5.agrees.external (by simp [mulR64Effect_components, Component.Covers])).trans mem4
  have g5r0 : ((Operand.reg 0 : Operand 64).read u5) = p0.1 := by
    have h := e5.writes.1
    change ((Operand.reg 0 : Operand 64).read u5) = ((Operand.reg 0 : Operand 64).read u4) * ((Operand.reg 11 : Operand 64).read u4) at h
    rw [g4r11, g4r0] at h
    simpa only [p0, product64] using h
  have g5r2 : ((Operand.reg 2 : Operand 64).read u5) = p0.2 := by
    have h := e5.writes.2
    change ((Operand.reg 2 : Operand 64).read u5) = mulHigh64 ((Operand.reg 0 : Operand 64).read u4) ((Operand.reg 11 : Operand 64).read u4) at h
    rw [g4r11, g4r0] at h
    simpa only [p0, product64] using h
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (mov_r64_r64_effect_step 0x1135a1 0x48 0xd3 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x135a1 _ (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135a4 (by decide)))
  change (movR64R64Effect 0x1135a1 3 2 u5).Holds u5 u6 at e6
  have f6 := f5.after_registers ready6 e6.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have mem6 : u6.external = t.external := (e6.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem5
  have g6r3 : ((Operand.reg 3 : Operand 64).read u6) = p0.2 := by
    have h := e6.writes
    change ((Operand.reg 3 : Operand 64).read u6) = ((Operand.reg 2 : Operand 64).read u5) at h
    rw [g5r2] at h
    simpa only [p0, product64] using h
  have g6r0 : ((Operand.reg 0 : Operand 64).read u6) = p0.1 := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r0
  obtain ⟨u7, run7, ready7, e7⟩ :=
    (mov_r64_r64_effect_step 0x1135a4 0x48 0xc1 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x135a4 _ (by decide) (by decide +kernel))
      e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135a7 (by decide)))
  change (movR64R64Effect 0x1135a4 1 0 u6).Holds u6 u7 at e7
  have f7 := f6.after_registers ready7 e7.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have mem7 : u7.external = t.external := (e7.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem6
  have g7r1 : ((Operand.reg 1 : Operand 64).read u7) = p0.1 := by
    have h := e7.writes
    change ((Operand.reg 1 : Operand 64).read u7) = ((Operand.reg 0 : Operand 64).read u6) at h
    rw [g6r0] at h
    simpa only [p0, product64] using h
  have g1r6 : ((Operand.reg 6 : Operand 64).read u1) = 0xffffffff := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r6
  have g2r6 : ((Operand.reg 6 : Operand 64).read u2) = 0xffffffff := (e2.agrees.read (by simp [imulR64R64Effect_components])).trans g1r6
  have g3r6 : ((Operand.reg 6 : Operand 64).read u3) = 0xffffffff := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r6
  have g4r6 : ((Operand.reg 6 : Operand 64).read u4) = 0xffffffff := (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r6
  have g5r6 : ((Operand.reg 6 : Operand 64).read u5) = 0xffffffff := (e5.agrees.read (by simp [mulR64Effect_components])).trans g4r6
  have g6r6 : ((Operand.reg 6 : Operand 64).read u6) = 0xffffffff := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r6
  have g7r6 : ((Operand.reg 6 : Operand 64).read u7) = 0xffffffff := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r6
  obtain ⟨u8, run8, ready8, e8⟩ :=
    (mov_r64_r64_effect_step 0x1135a7 0x48 0xf0 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x135a7 _ (by decide) (by decide +kernel))
      e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135aa (by decide)))
  change (movR64R64Effect 0x1135a7 0 6 u7).Holds u7 u8 at e8
  have f8 := f7.after_registers ready8 e8.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have mem8 : u8.external = t.external := (e8.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem7
  have g8r0 : ((Operand.reg 0 : Operand 64).read u8) = 0xffffffff := by
    have h := e8.writes
    change ((Operand.reg 0 : Operand 64).read u8) = ((Operand.reg 6 : Operand 64).read u7) at h
    rw [g7r6] at h
    exact h
  have g3r8 : ((Operand.reg 8 : Operand 64).read u3) = a.l0 := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r8
  have g4r8 : ((Operand.reg 8 : Operand 64).read u4) = a.l0 := (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r8
  have g5r8 : ((Operand.reg 8 : Operand 64).read u5) = a.l0 := (e5.agrees.read (by simp [mulR64Effect_components])).trans g4r8
  have g6r8 : ((Operand.reg 8 : Operand 64).read u6) = a.l0 := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r8
  have g7r8 : ((Operand.reg 8 : Operand 64).read u7) = a.l0 := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r8
  have g8r8 : ((Operand.reg 8 : Operand 64).read u8) = a.l0 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r8
  obtain ⟨u9, run9, ready9, e9⟩ :=
    (mul_r64_effect_step 0x1135aa 0x49 0xe0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x135aa _ (by decide) (by decide +kernel))
      e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135ad (by decide)))
  change (mulR64Effect 0x1135aa 8 u8).Holds u8 u9 at e9
  have f9 := f8.after_registers ready9 e9.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have mem9 : u9.external = t.external := (e9.agrees.external (by simp [mulR64Effect_components, Component.Covers])).trans mem8
  have g9r0 : ((Operand.reg 0 : Operand 64).read u9) = p1.1 := by
    have h := e9.writes.1
    change ((Operand.reg 0 : Operand 64).read u9) = ((Operand.reg 0 : Operand 64).read u8) * ((Operand.reg 8 : Operand 64).read u8) at h
    rw [g8r8, g8r0] at h
    simpa only [p1, product64] using h
  have g9r2 : ((Operand.reg 2 : Operand 64).read u9) = p1.2 := by
    have h := e9.writes.2
    change ((Operand.reg 2 : Operand 64).read u9) = mulHigh64 ((Operand.reg 0 : Operand 64).read u8) ((Operand.reg 8 : Operand 64).read u8) at h
    rw [g8r8, g8r0] at h
    simpa only [p1, product64] using h
  have g9r8 : ((Operand.reg 8 : Operand 64).read u9) = a.l0 := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r8
  obtain ⟨u10, run10, ready10, e10⟩ :=
    (mov_r64_r64_effect_step 0x1135ad 0x4d 0xc2 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x135ad _ (by decide) (by decide +kernel))
      e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135b0 (by decide)))
  change (movR64R64Effect 0x1135ad 10 8 u9).Holds u9 u10 at e10
  have f10 := f9.after_registers ready10 e10.agrees (by simp [movR64R64Effect_components, Component.Covers]) (by simp [movR64R64Effect_components])
  have mem10 : u10.external = t.external := (e10.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem9
  have g10r10 : ((Operand.reg 10 : Operand 64).read u10) = a.l0 := by
    have h := e10.writes
    change ((Operand.reg 10 : Operand 64).read u10) = ((Operand.reg 8 : Operand 64).read u9) at h
    rw [g9r8] at h
    exact h
  have g2r12 : ((Operand.reg 12 : Operand 64).read u2) = a.l0 := (e2.agrees.read (by simp [imulR64R64Effect_components])).trans g1r12
  have g3r12 : ((Operand.reg 12 : Operand 64).read u3) = a.l0 := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r12
  have g4r12 : ((Operand.reg 12 : Operand 64).read u4) = a.l0 := (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r12
  have g5r12 : ((Operand.reg 12 : Operand 64).read u5) = a.l0 := (e5.agrees.read (by simp [mulR64Effect_components])).trans g4r12
  have g6r12 : ((Operand.reg 12 : Operand 64).read u6) = a.l0 := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r12
  have g7r12 : ((Operand.reg 12 : Operand 64).read u7) = a.l0 := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r12
  have g8r12 : ((Operand.reg 12 : Operand 64).read u8) = a.l0 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r12
  have g9r12 : ((Operand.reg 12 : Operand 64).read u9) = a.l0 := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r12
  have g10r12 : ((Operand.reg 12 : Operand 64).read u10) = a.l0 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r12
  have g8r1 : ((Operand.reg 1 : Operand 64).read u8) = p0.1 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r1
  have g9r1 : ((Operand.reg 1 : Operand 64).read u9) = p0.1 := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r1
  have g10r1 : ((Operand.reg 1 : Operand 64).read u10) = p0.1 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r1
  obtain ⟨u11, run11, ready11, e11⟩ :=
    (add_r64_r64_effect_step 0x1135b0 0x4c 0xe1 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x135b0 _ (by decide) (by decide +kernel))
      e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135b3 (by decide)))
  change (addR64R64Effect 0x1135b0 1 12 u10).Holds u10 u11 at e11
  have f11 := f10.after_registers ready11 e11.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have mem11 : u11.external = t.external := (e11.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem10
  have g11r1 : ((Operand.reg 1 : Operand 64).read u11) = z.1 := by
    have h := e11.writes
    change ((Operand.reg 1 : Operand 64).read u11) = (addSpec ((Operand.reg 1 : Operand 64).read u10) ((Operand.reg 12 : Operand 64).read u10)).1 at h
    rw [g10r12, g10r1] at h
    simpa only [z, add64] using h
  have cf11 : (StatusFlags.ofRFLAGS u11.RFLAGS).CF = z.2 := by
    have h := e11.flags.1
    change (StatusFlags.ofRFLAGS u11.RFLAGS).CF = (addSpec ((Operand.reg 1 : Operand 64).read u10) ((Operand.reg 12 : Operand 64).read u10)).2.CF at h
    rw [g10r12, g10r1] at h
    simpa only [z, add64] using h
  have g1r15 : ((Operand.reg 15 : Operand 64).read u1) = a.l1 := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r15
  have g2r15 : ((Operand.reg 15 : Operand 64).read u2) = a.l1 := (e2.agrees.read (by simp [imulR64R64Effect_components])).trans g1r15
  have g3r15 : ((Operand.reg 15 : Operand 64).read u3) = a.l1 := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r15
  have g4r15 : ((Operand.reg 15 : Operand 64).read u4) = a.l1 := (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r15
  have g5r15 : ((Operand.reg 15 : Operand 64).read u5) = a.l1 := (e5.agrees.read (by simp [mulR64Effect_components])).trans g4r15
  have g6r15 : ((Operand.reg 15 : Operand 64).read u6) = a.l1 := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r15
  have g7r15 : ((Operand.reg 15 : Operand 64).read u7) = a.l1 := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r15
  have g8r15 : ((Operand.reg 15 : Operand 64).read u8) = a.l1 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r15
  have g9r15 : ((Operand.reg 15 : Operand 64).read u9) = a.l1 := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r15
  have g10r15 : ((Operand.reg 15 : Operand 64).read u10) = a.l1 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r15
  have g11r15 : ((Operand.reg 15 : Operand 64).read u11) = a.l1 := (e11.agrees.read (by simp [addR64R64Effect_components])).trans g10r15
  have g7r3 : ((Operand.reg 3 : Operand 64).read u7) = p0.2 := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r3
  have g8r3 : ((Operand.reg 3 : Operand 64).read u8) = p0.2 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r3
  have g9r3 : ((Operand.reg 3 : Operand 64).read u9) = p0.2 := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r3
  have g10r3 : ((Operand.reg 3 : Operand 64).read u10) = p0.2 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r3
  have g11r3 : ((Operand.reg 3 : Operand 64).read u11) = p0.2 := (e11.agrees.read (by simp [addR64R64Effect_components])).trans g10r3
  obtain ⟨u12, run12, ready12, e12⟩ :=
    (adc_r64_r64_effect_step 0x1135b3 0x4c 0xfb (by simp [RexWPrefix]) (by decide)).advances (readyToStep f11.machine f11.bindingsSupported)
      (programText_slice (programLoaded_codeIn f11.loaded) 0x135b3 _ (by decide) (by decide +kernel))
      e11.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135b6 (by decide)))
  change (adcR64R64Effect 0x1135b3 3 15 u11).Holds u11 u12 at e12
  have f12 := f11.after_registers ready12 e12.agrees (by simp [adcR64R64Effect_components, Component.Covers]) (by simp [adcR64R64Effect_components])
  have mem12 : u12.external = t.external := (e12.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans mem11
  have g12r3 : ((Operand.reg 3 : Operand 64).read u12) = y.1 := by
    have h := e12.writes
    change ((Operand.reg 3 : Operand 64).read u12) = (adcSpec ((Operand.reg 3 : Operand 64).read u11) ((Operand.reg 15 : Operand 64).read u11) (u11.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g11r15, g11r3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf11] at h
    simpa only [y, adc64] using h
  have cf12 : (StatusFlags.ofRFLAGS u12.RFLAGS).CF = y.2 := by
    have h := e12.flags.1
    change (StatusFlags.ofRFLAGS u12.RFLAGS).CF = (adcSpec ((Operand.reg 3 : Operand 64).read u11) ((Operand.reg 15 : Operand 64).read u11) (u11.RFLAGS.extractLsb' 0 1)).2.CF at h
    rw [g11r15, g11r3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf11] at h
    simpa only [y, adc64] using h
  have g12r1 : ((Operand.reg 1 : Operand 64).read u12) = z.1 := (e12.agrees.read (by simp [adcR64R64Effect_components])).trans g11r1
  obtain ⟨u13, run13, ready13, e13⟩ :=
    (setcc_r8_effect_step 0x1135b6 0x92 0xc1 (by simp [SupportedOpcode]) (by decide) (by decide)).advances (readyToStep f12.machine f12.bindingsSupported)
      (programText_slice (programLoaded_codeIn f12.loaded) 0x135b6 _ (by decide) (by decide +kernel))
      e12.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135b9 (by decide)))
  change (setccR8Effect 0x1135b6 3 1 2 u12).Holds u12 u13 at e13
  have f13 := f12.after_registers ready13 e13.agrees (by simp [setccR8Effect_components, Component.Covers]) (by simp [setccR8Effect_components])
  have mem13 : u13.external = t.external := (e13.agrees.external (by simp [setccR8Effect_components, Component.Covers])).trans mem12
  have g13r1 : ((Operand.reg 1 : Operand 64).read u13) = (mergeGPR 8 (if y.2 then 1 else 0) (z.1)) := by
    have h := e13.writes
    change ((Operand.reg 1 : Operand 64).read u13) = mergeGPR 8 (if (StatusFlags.ofRFLAGS u12.RFLAGS).CF then 1 else 0) ((Operand.reg 1 : Operand 64).read u12) at h
    rw [g12r1, cf12] at h
    exact h
  obtain ⟨u14, run14, ready14, e14⟩ :=
    (movzx_r32_r8_effect_step 0x1135b9 0xc9 (by decide) (by decide)).advances (readyToStep f13.machine f13.bindingsSupported)
      (programText_slice (programLoaded_codeIn f13.loaded) 0x135b9 _ (by decide) (by decide +kernel))
      e13.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135bc (by decide)))
  change (movzxR32R8Effect 0x1135b9 3 1 1 u13).Holds u13 u14 at e14
  have f14 := f13.after_registers ready14 e14.agrees (by simp [movzxR32R8Effect_components, Component.Covers]) (by simp [movzxR32R8Effect_components])
  have mem14 : u14.external = t.external := (e14.agrees.external (by simp [movzxR32R8Effect_components, Component.Covers])).trans mem13
  have g14r1 : ((Operand.reg 1 : Operand 64).read u14) = BitVec.ofNat 64 y.2.toNat := by
    have h := e14.writes
    change ((Operand.reg 1 : Operand 64).read u14) = (((Operand.reg 1 : Operand 64).read u13).setWidth 8).setWidth 64 at h
    rw [g13r1] at h
    simpa only [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, bool_byte] using h
  obtain ⟨u15, run15, ready15, e15⟩ :=
    (mov_r64_m64_effect_step 0x1135bc 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl).advances (readyToStep f14.machine f14.bindingsSupported)
      (programText_slice (programLoaded_codeIn f14.loaded) 0x135bc _ (by decide) (by decide +kernel))
      ⟨e14.rip, ScalarFrame.stack_readable pre.toCalleePre f14 (offset := 24) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135c1 (by decide)))
  change (movR64M64Effect 0x1135bc 6 (.sib 4 none 0 (.d8 24)) u14).Holds u14 u15 at e15
  have f15 := f14.after_registers ready15 e15.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have mem15 : u15.external = t.external := (e15.agrees.external (by simp [movR64M64Effect_components, Component.Covers])).trans mem14
  have load15 : memLoad u14.external (((Operand.reg 4 : Operand 64).read u14) + 24) 64 = s.regValue .rsi := by
    change memLoad u14.external (stackPtr u14 + 24) 64 = _
    rw [f14.rsp, mem14]
    exact state.inputPointer
  have g15r6 : ((Operand.reg 6 : Operand 64).read u15) = s.regValue .rsi := by
    have h := e15.writes
    change ((Operand.reg 6 : Operand 64).read u15) = memLoad u14.external (((Operand.reg 4 : Operand 64).read u14) + 24) 64 at h
    rw [load15] at h
    exact h
  obtain ⟨u16, run16, ready16, e16⟩ :=
    (mov_r64_m64_effect_step 0x1135c1 0x4c (by simp [RexWPrefix]) 6 (.base 6 (.d8 48)) (by decide) rfl rfl).advances (readyToStep f15.machine f15.bindingsSupported)
      (programText_slice (programLoaded_codeIn f15.loaded) 0x135c1 _ (by decide) (by decide +kernel))
      ⟨e15.rip, by
        change MemReadable u15 (((Operand.reg 6 : Operand 64).read u15) + 48) 8
        rw [g15r6]
        exact input_readable pre f15 (j := 6) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135c5 (by decide)))
  change (movR64M64Effect 0x1135c1 14 (.base 6 (.d8 48)) u15).Holds u15 u16 at e16
  have f16 := f15.after_registers ready16 e16.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have mem16 : u16.external = t.external := (e16.agrees.external (by simp [movR64M64Effect_components, Component.Covers])).trans mem15
  have load16 : memLoad u15.external (((Operand.reg 6 : Operand 64).read u15) + 48) 64 = extra := by
    rw [g15r6]
    exact input_limb pre f15 input 6 (by decide)
  have g16r14 : ((Operand.reg 14 : Operand 64).read u16) = extra := by
    have h := e16.writes
    change ((Operand.reg 14 : Operand 64).read u16) = memLoad u15.external (((Operand.reg 6 : Operand 64).read u15) + 48) 64 at h
    rw [load16] at h
    exact h
  have g10r0 : ((Operand.reg 0 : Operand 64).read u10) = p1.1 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r0
  have g11r0 : ((Operand.reg 0 : Operand 64).read u11) = p1.1 := (e11.agrees.read (by simp [addR64R64Effect_components])).trans g10r0
  have g12r0 : ((Operand.reg 0 : Operand 64).read u12) = p1.1 := (e12.agrees.read (by simp [adcR64R64Effect_components])).trans g11r0
  have g13r0 : ((Operand.reg 0 : Operand 64).read u13) = p1.1 := (e13.agrees.read (by simp [setccR8Effect_components])).trans g12r0
  have g14r0 : ((Operand.reg 0 : Operand 64).read u14) = p1.1 := (e14.agrees.read (by simp [movzxR32R8Effect_components])).trans g13r0
  have g15r0 : ((Operand.reg 0 : Operand 64).read u15) = p1.1 := (e15.agrees.read (by simp [movR64M64Effect_components])).trans g14r0
  have g16r0 : ((Operand.reg 0 : Operand 64).read u16) = p1.1 := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r0
  have g13r3 : ((Operand.reg 3 : Operand 64).read u13) = y.1 := (e13.agrees.read (by simp [setccR8Effect_components])).trans g12r3
  have g14r3 : ((Operand.reg 3 : Operand 64).read u14) = y.1 := (e14.agrees.read (by simp [movzxR32R8Effect_components])).trans g13r3
  have g15r3 : ((Operand.reg 3 : Operand 64).read u15) = y.1 := (e15.agrees.read (by simp [movR64M64Effect_components])).trans g14r3
  have g16r3 : ((Operand.reg 3 : Operand 64).read u16) = y.1 := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r3
  obtain ⟨u17, run17, ready17, e17⟩ :=
    (add_r64_r64_effect_step 0x1135c5 0x48 0xc3 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f16.machine f16.bindingsSupported)
      (programText_slice (programLoaded_codeIn f16.loaded) 0x135c5 _ (by decide) (by decide +kernel))
      e16.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135c8 (by decide)))
  change (addR64R64Effect 0x1135c5 3 0 u16).Holds u16 u17 at e17
  have f17 := f16.after_registers ready17 e17.agrees (by simp [addR64R64Effect_components, Component.Covers]) (by simp [addR64R64Effect_components])
  have mem17 : u17.external = t.external := (e17.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem16
  have g17r3 : ((Operand.reg 3 : Operand 64).read u17) = x.1 := by
    have h := e17.writes
    change ((Operand.reg 3 : Operand 64).read u17) = (addSpec ((Operand.reg 3 : Operand 64).read u16) ((Operand.reg 0 : Operand 64).read u16)).1 at h
    rw [g16r0, g16r3] at h
    simpa only [x, add64] using h
  have cf17 : (StatusFlags.ofRFLAGS u17.RFLAGS).CF = x.2 := by
    have h := e17.flags.1
    change (StatusFlags.ofRFLAGS u17.RFLAGS).CF = (addSpec ((Operand.reg 3 : Operand 64).read u16) ((Operand.reg 0 : Operand 64).read u16)).2.CF at h
    rw [g16r0, g16r3] at h
    simpa only [x, add64] using h
  have g10r2 : ((Operand.reg 2 : Operand 64).read u10) = p1.2 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r2
  have g11r2 : ((Operand.reg 2 : Operand 64).read u11) = p1.2 := (e11.agrees.read (by simp [addR64R64Effect_components])).trans g10r2
  have g12r2 : ((Operand.reg 2 : Operand 64).read u12) = p1.2 := (e12.agrees.read (by simp [adcR64R64Effect_components])).trans g11r2
  have g13r2 : ((Operand.reg 2 : Operand 64).read u13) = p1.2 := (e13.agrees.read (by simp [setccR8Effect_components])).trans g12r2
  have g14r2 : ((Operand.reg 2 : Operand 64).read u14) = p1.2 := (e14.agrees.read (by simp [movzxR32R8Effect_components])).trans g13r2
  have g15r2 : ((Operand.reg 2 : Operand 64).read u15) = p1.2 := (e15.agrees.read (by simp [movR64M64Effect_components])).trans g14r2
  have g16r2 : ((Operand.reg 2 : Operand 64).read u16) = p1.2 := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r2
  have g17r2 : ((Operand.reg 2 : Operand 64).read u17) = p1.2 := (e17.agrees.read (by simp [addR64R64Effect_components])).trans g16r2
  have g15r1 : ((Operand.reg 1 : Operand 64).read u15) = BitVec.ofNat 64 y.2.toNat := (e15.agrees.read (by simp [movR64M64Effect_components])).trans g14r1
  have g16r1 : ((Operand.reg 1 : Operand 64).read u16) = BitVec.ofNat 64 y.2.toNat := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r1
  have g17r1 : ((Operand.reg 1 : Operand 64).read u17) = BitVec.ofNat 64 y.2.toNat := (e17.agrees.read (by simp [addR64R64Effect_components])).trans g16r1
  obtain ⟨u18, run18, ready18, e18⟩ :=
    (adc_r64_r64_effect_step 0x1135c8 0x48 0xd1 (by simp [RexWPrefix]) (by decide)).advances (readyToStep f17.machine f17.bindingsSupported)
      (programText_slice (programLoaded_codeIn f17.loaded) 0x135c8 _ (by decide) (by decide +kernel))
      e17.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135cb (by decide)))
  change (adcR64R64Effect 0x1135c8 1 2 u17).Holds u17 u18 at e18
  have f18 := f17.after_registers ready18 e18.agrees (by simp [adcR64R64Effect_components, Component.Covers]) (by simp [adcR64R64Effect_components])
  have mem18 : u18.external = t.external := (e18.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans mem17
  have g18r1 : ((Operand.reg 1 : Operand 64).read u18) = k.1 := by
    have h := e18.writes
    change ((Operand.reg 1 : Operand 64).read u18) = (adcSpec ((Operand.reg 1 : Operand 64).read u17) ((Operand.reg 2 : Operand 64).read u17) (u17.RFLAGS.extractLsb' 0 1)).1 at h
    rw [g17r2, g17r1, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf17] at h
    simpa only [k, adc64] using h
  obtain ⟨u19, run19, ready19, e19⟩ :=
    (mov_r64_m64_effect_step 0x1135cb 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl).advances (readyToStep f18.machine f18.bindingsSupported)
      (programText_slice (programLoaded_codeIn f18.loaded) 0x135cb _ (by decide) (by decide +kernel))
      ⟨e18.rip, ScalarFrame.stack_readable pre.toCalleePre f18 (offset := 40) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135d0 (by decide)))
  change (movR64M64Effect 0x1135cb 0 (.sib 4 none 0 (.d8 40)) u18).Holds u18 u19 at e19
  have f19 := f18.after_registers ready19 e19.agrees (by simp [movR64M64Effect_components, Component.Covers]) (by simp [movR64M64Effect_components])
  have mem19 : u19.external = t.external := (e19.agrees.external (by simp [movR64M64Effect_components, Component.Covers])).trans mem18
  have load19 : memLoad u18.external (((Operand.reg 4 : Operand 64).read u18) + 40) 64 = 0 := by
    change memLoad u18.external (stackPtr u18 + 40) 64 = _
    rw [f18.rsp, mem18]
    exact state.slots.p2
  have g19r0 : ((Operand.reg 0 : Operand 64).read u19) = 0 := by
    have h := e19.writes
    change ((Operand.reg 0 : Operand 64).read u19) = memLoad u18.external (((Operand.reg 4 : Operand 64).read u18) + 40) 64 at h
    rw [load19] at h
    exact h
  have g10r8 : ((Operand.reg 8 : Operand 64).read u10) = a.l0 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r8
  have g11r8 : ((Operand.reg 8 : Operand 64).read u11) = a.l0 := (e11.agrees.read (by simp [addR64R64Effect_components])).trans g10r8
  have g12r8 : ((Operand.reg 8 : Operand 64).read u12) = a.l0 := (e12.agrees.read (by simp [adcR64R64Effect_components])).trans g11r8
  have g13r8 : ((Operand.reg 8 : Operand 64).read u13) = a.l0 := (e13.agrees.read (by simp [setccR8Effect_components])).trans g12r8
  have g14r8 : ((Operand.reg 8 : Operand 64).read u14) = a.l0 := (e14.agrees.read (by simp [movzxR32R8Effect_components])).trans g13r8
  have g15r8 : ((Operand.reg 8 : Operand 64).read u15) = a.l0 := (e15.agrees.read (by simp [movR64M64Effect_components])).trans g14r8
  have g16r8 : ((Operand.reg 8 : Operand 64).read u16) = a.l0 := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r8
  have g17r8 : ((Operand.reg 8 : Operand 64).read u17) = a.l0 := (e17.agrees.read (by simp [addR64R64Effect_components])).trans g16r8
  have g18r8 : ((Operand.reg 8 : Operand 64).read u18) = a.l0 := (e18.agrees.read (by simp [adcR64R64Effect_components])).trans g17r8
  have g19r8 : ((Operand.reg 8 : Operand 64).read u19) = a.l0 := (e19.agrees.read (by simp [movR64M64Effect_components])).trans g18r8
  obtain ⟨u20, run20, ready20, e20⟩ :=
    (mul_r64_effect_step 0x1135d0 0x49 0xe0 (by simp [RexWPrefix]) (by decide) (by decide)).advances (readyToStep f19.machine f19.bindingsSupported)
      (programText_slice (programLoaded_codeIn f19.loaded) 0x135d0 _ (by decide) (by decide +kernel))
      e19.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135d3 (by decide)))
  change (mulR64Effect 0x1135d0 8 u19).Holds u19 u20 at e20
  have f20 := f19.after_registers ready20 e20.agrees (by simp [mulR64Effect_components, Component.Covers]) (by simp [mulR64Effect_components])
  have mem20 : u20.external = t.external := (e20.agrees.external (by simp [mulR64Effect_components, Component.Covers])).trans mem19
  have g20r0 : ((Operand.reg 0 : Operand 64).read u20) = 0 := by
    have h := e20.writes.1
    change ((Operand.reg 0 : Operand 64).read u20) = ((Operand.reg 0 : Operand 64).read u19) * ((Operand.reg 8 : Operand 64).read u19) at h
    rw [g19r8, g19r0] at h
    simpa [mulHigh64] using h
  have g20r2 : ((Operand.reg 2 : Operand 64).read u20) = 0 := by
    have h := e20.writes.2
    change ((Operand.reg 2 : Operand 64).read u20) = mulHigh64 ((Operand.reg 0 : Operand 64).read u19) ((Operand.reg 8 : Operand 64).read u19) at h
    rw [g19r8, g19r0] at h
    simpa [mulHigh64] using h
  have g20r8 : ((Operand.reg 8 : Operand 64).read u20) = a.l0 := (e20.agrees.read (by simp [mulR64Effect_components])).trans g19r8
  obtain ⟨u21, run21, ready21, e21⟩ :=
    (xor_r32_r32_rex_effect_step 0x1135d3 0x45 0xc0 (by simp [RexNoWPrefix]) (by decide)).advances (readyToStep f20.machine f20.bindingsSupported)
      (programText_slice (programLoaded_codeIn f20.loaded) 0x135d3 _ (by decide) (by decide +kernel))
      e20.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x135d6 (by decide)))
  change (xorR32R32Effect 0x1135d3 3 8 8 u20).Holds u20 u21 at e21
  have f21 := f20.after_registers ready21 e21.agrees (by simp [xorR32R32Effect_components, Component.Covers]) (by simp [xorR32R32Effect_components])
  have mem21 : u21.external = t.external := (e21.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])).trans mem20
  have g21r8 : ((Operand.reg 8 : Operand 64).read u21) = 0 := by
    have h := e21.writes
    change ((Operand.reg 8 : Operand 64).read u21) = (((((Operand.reg 8 : Operand 64).read u20)).setWidth 32 ^^^ (((Operand.reg 8 : Operand 64).read u20)).setWidth 32).setWidth 64) at h
    rw [g20r8] at h
    simpa using h
  have g1r7 : ((Operand.reg 7 : Operand 64).read u1) = s.regValue .rdi := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r7
  have g2r7 : ((Operand.reg 7 : Operand 64).read u2) = s.regValue .rdi := (e2.agrees.read (by simp [imulR64R64Effect_components])).trans g1r7
  have g3r7 : ((Operand.reg 7 : Operand 64).read u3) = s.regValue .rdi := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r7
  have g4r7 : ((Operand.reg 7 : Operand 64).read u4) = s.regValue .rdi := (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r7
  have g5r7 : ((Operand.reg 7 : Operand 64).read u5) = s.regValue .rdi := (e5.agrees.read (by simp [mulR64Effect_components])).trans g4r7
  have g6r7 : ((Operand.reg 7 : Operand 64).read u6) = s.regValue .rdi := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r7
  have g7r7 : ((Operand.reg 7 : Operand 64).read u7) = s.regValue .rdi := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r7
  have g8r7 : ((Operand.reg 7 : Operand 64).read u8) = s.regValue .rdi := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r7
  have g9r7 : ((Operand.reg 7 : Operand 64).read u9) = s.regValue .rdi := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r7
  have g10r7 : ((Operand.reg 7 : Operand 64).read u10) = s.regValue .rdi := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r7
  have g11r7 : ((Operand.reg 7 : Operand 64).read u11) = s.regValue .rdi := (e11.agrees.read (by simp [addR64R64Effect_components])).trans g10r7
  have g12r7 : ((Operand.reg 7 : Operand 64).read u12) = s.regValue .rdi := (e12.agrees.read (by simp [adcR64R64Effect_components])).trans g11r7
  have g13r7 : ((Operand.reg 7 : Operand 64).read u13) = s.regValue .rdi := (e13.agrees.read (by simp [setccR8Effect_components])).trans g12r7
  have g14r7 : ((Operand.reg 7 : Operand 64).read u14) = s.regValue .rdi := (e14.agrees.read (by simp [movzxR32R8Effect_components])).trans g13r7
  have g15r7 : ((Operand.reg 7 : Operand 64).read u15) = s.regValue .rdi := (e15.agrees.read (by simp [movR64M64Effect_components])).trans g14r7
  have g16r7 : ((Operand.reg 7 : Operand 64).read u16) = s.regValue .rdi := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r7
  have g17r7 : ((Operand.reg 7 : Operand 64).read u17) = s.regValue .rdi := (e17.agrees.read (by simp [addR64R64Effect_components])).trans g16r7
  have g18r7 : ((Operand.reg 7 : Operand 64).read u18) = s.regValue .rdi := (e18.agrees.read (by simp [adcR64R64Effect_components])).trans g17r7
  have g19r7 : ((Operand.reg 7 : Operand 64).read u19) = s.regValue .rdi := (e19.agrees.read (by simp [movR64M64Effect_components])).trans g18r7
  have g20r7 : ((Operand.reg 7 : Operand 64).read u20) = s.regValue .rdi := (e20.agrees.read (by simp [mulR64Effect_components])).trans g19r7
  have g21r7 : ((Operand.reg 7 : Operand 64).read u21) = s.regValue .rdi := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r7
  have g5r11 : ((Operand.reg 11 : Operand 64).read u5) = 0xffffffffffffffff := (e5.agrees.read (by simp [mulR64Effect_components])).trans g4r11
  have g6r11 : ((Operand.reg 11 : Operand 64).read u6) = 0xffffffffffffffff := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r11
  have g7r11 : ((Operand.reg 11 : Operand 64).read u7) = 0xffffffffffffffff := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r11
  have g8r11 : ((Operand.reg 11 : Operand 64).read u8) = 0xffffffffffffffff := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r11
  have g9r11 : ((Operand.reg 11 : Operand 64).read u9) = 0xffffffffffffffff := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r11
  have g10r11 : ((Operand.reg 11 : Operand 64).read u10) = 0xffffffffffffffff := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r11
  have g11r11 : ((Operand.reg 11 : Operand 64).read u11) = 0xffffffffffffffff := (e11.agrees.read (by simp [addR64R64Effect_components])).trans g10r11
  have g12r11 : ((Operand.reg 11 : Operand 64).read u12) = 0xffffffffffffffff := (e12.agrees.read (by simp [adcR64R64Effect_components])).trans g11r11
  have g13r11 : ((Operand.reg 11 : Operand 64).read u13) = 0xffffffffffffffff := (e13.agrees.read (by simp [setccR8Effect_components])).trans g12r11
  have g14r11 : ((Operand.reg 11 : Operand 64).read u14) = 0xffffffffffffffff := (e14.agrees.read (by simp [movzxR32R8Effect_components])).trans g13r11
  have g15r11 : ((Operand.reg 11 : Operand 64).read u15) = 0xffffffffffffffff := (e15.agrees.read (by simp [movR64M64Effect_components])).trans g14r11
  have g16r11 : ((Operand.reg 11 : Operand 64).read u16) = 0xffffffffffffffff := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r11
  have g17r11 : ((Operand.reg 11 : Operand 64).read u17) = 0xffffffffffffffff := (e17.agrees.read (by simp [addR64R64Effect_components])).trans g16r11
  have g18r11 : ((Operand.reg 11 : Operand 64).read u18) = 0xffffffffffffffff := (e18.agrees.read (by simp [adcR64R64Effect_components])).trans g17r11
  have g19r11 : ((Operand.reg 11 : Operand 64).read u19) = 0xffffffffffffffff := (e19.agrees.read (by simp [movR64M64Effect_components])).trans g18r11
  have g20r11 : ((Operand.reg 11 : Operand 64).read u20) = 0xffffffffffffffff := (e20.agrees.read (by simp [mulR64Effect_components])).trans g19r11
  have g21r11 : ((Operand.reg 11 : Operand 64).read u21) = 0xffffffffffffffff := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r11
  have g16r6 : ((Operand.reg 6 : Operand 64).read u16) = s.regValue .rsi := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r6
  have g17r6 : ((Operand.reg 6 : Operand 64).read u17) = s.regValue .rsi := (e17.agrees.read (by simp [addR64R64Effect_components])).trans g16r6
  have g18r6 : ((Operand.reg 6 : Operand 64).read u18) = s.regValue .rsi := (e18.agrees.read (by simp [adcR64R64Effect_components])).trans g17r6
  have g19r6 : ((Operand.reg 6 : Operand 64).read u19) = s.regValue .rsi := (e19.agrees.read (by simp [movR64M64Effect_components])).trans g18r6
  have g20r6 : ((Operand.reg 6 : Operand 64).read u20) = s.regValue .rsi := (e20.agrees.read (by simp [mulR64Effect_components])).trans g19r6
  have g21r6 : ((Operand.reg 6 : Operand 64).read u21) = s.regValue .rsi := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r6
  have g1r5 : ((Operand.reg 5 : Operand 64).read u1) = 0xffffffff00000001 := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r5
  have g2r5 : ((Operand.reg 5 : Operand 64).read u2) = 0xffffffff00000001 := (e2.agrees.read (by simp [imulR64R64Effect_components])).trans g1r5
  have g3r5 : ((Operand.reg 5 : Operand 64).read u3) = 0xffffffff00000001 := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r5
  have g4r5 : ((Operand.reg 5 : Operand 64).read u4) = 0xffffffff00000001 := (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r5
  have g5r5 : ((Operand.reg 5 : Operand 64).read u5) = 0xffffffff00000001 := (e5.agrees.read (by simp [mulR64Effect_components])).trans g4r5
  have g6r5 : ((Operand.reg 5 : Operand 64).read u6) = 0xffffffff00000001 := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r5
  have g7r5 : ((Operand.reg 5 : Operand 64).read u7) = 0xffffffff00000001 := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r5
  have g8r5 : ((Operand.reg 5 : Operand 64).read u8) = 0xffffffff00000001 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r5
  have g9r5 : ((Operand.reg 5 : Operand 64).read u9) = 0xffffffff00000001 := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r5
  have g10r5 : ((Operand.reg 5 : Operand 64).read u10) = 0xffffffff00000001 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r5
  have g11r5 : ((Operand.reg 5 : Operand 64).read u11) = 0xffffffff00000001 := (e11.agrees.read (by simp [addR64R64Effect_components])).trans g10r5
  have g12r5 : ((Operand.reg 5 : Operand 64).read u12) = 0xffffffff00000001 := (e12.agrees.read (by simp [adcR64R64Effect_components])).trans g11r5
  have g13r5 : ((Operand.reg 5 : Operand 64).read u13) = 0xffffffff00000001 := (e13.agrees.read (by simp [setccR8Effect_components])).trans g12r5
  have g14r5 : ((Operand.reg 5 : Operand 64).read u14) = 0xffffffff00000001 := (e14.agrees.read (by simp [movzxR32R8Effect_components])).trans g13r5
  have g15r5 : ((Operand.reg 5 : Operand 64).read u15) = 0xffffffff00000001 := (e15.agrees.read (by simp [movR64M64Effect_components])).trans g14r5
  have g16r5 : ((Operand.reg 5 : Operand 64).read u16) = 0xffffffff00000001 := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r5
  have g17r5 : ((Operand.reg 5 : Operand 64).read u17) = 0xffffffff00000001 := (e17.agrees.read (by simp [addR64R64Effect_components])).trans g16r5
  have g18r5 : ((Operand.reg 5 : Operand 64).read u18) = 0xffffffff00000001 := (e18.agrees.read (by simp [adcR64R64Effect_components])).trans g17r5
  have g19r5 : ((Operand.reg 5 : Operand 64).read u19) = 0xffffffff00000001 := (e19.agrees.read (by simp [movR64M64Effect_components])).trans g18r5
  have g20r5 : ((Operand.reg 5 : Operand 64).read u20) = 0xffffffff00000001 := (e20.agrees.read (by simp [mulR64Effect_components])).trans g19r5
  have g21r5 : ((Operand.reg 5 : Operand 64).read u21) = 0xffffffff00000001 := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r5
  have g19r1 : ((Operand.reg 1 : Operand 64).read u19) = k.1 := (e19.agrees.read (by simp [movR64M64Effect_components])).trans g18r1
  have g20r1 : ((Operand.reg 1 : Operand 64).read u20) = k.1 := (e20.agrees.read (by simp [mulR64Effect_components])).trans g19r1
  have g21r1 : ((Operand.reg 1 : Operand 64).read u21) = k.1 := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r1
  have g1r9 : ((Operand.reg 9 : Operand 64).read u1) = a.l3 := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r9
  have g2r9 : ((Operand.reg 9 : Operand 64).read u2) = a.l3 := (e2.agrees.read (by simp [imulR64R64Effect_components])).trans g1r9
  have g3r9 : ((Operand.reg 9 : Operand 64).read u3) = a.l3 := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r9
  have g4r9 : ((Operand.reg 9 : Operand 64).read u4) = a.l3 := (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r9
  have g5r9 : ((Operand.reg 9 : Operand 64).read u5) = a.l3 := (e5.agrees.read (by simp [mulR64Effect_components])).trans g4r9
  have g6r9 : ((Operand.reg 9 : Operand 64).read u6) = a.l3 := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r9
  have g7r9 : ((Operand.reg 9 : Operand 64).read u7) = a.l3 := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r9
  have g8r9 : ((Operand.reg 9 : Operand 64).read u8) = a.l3 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r9
  have g9r9 : ((Operand.reg 9 : Operand 64).read u9) = a.l3 := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r9
  have g10r9 : ((Operand.reg 9 : Operand 64).read u10) = a.l3 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r9
  have g11r9 : ((Operand.reg 9 : Operand 64).read u11) = a.l3 := (e11.agrees.read (by simp [addR64R64Effect_components])).trans g10r9
  have g12r9 : ((Operand.reg 9 : Operand 64).read u12) = a.l3 := (e12.agrees.read (by simp [adcR64R64Effect_components])).trans g11r9
  have g13r9 : ((Operand.reg 9 : Operand 64).read u13) = a.l3 := (e13.agrees.read (by simp [setccR8Effect_components])).trans g12r9
  have g14r9 : ((Operand.reg 9 : Operand 64).read u14) = a.l3 := (e14.agrees.read (by simp [movzxR32R8Effect_components])).trans g13r9
  have g15r9 : ((Operand.reg 9 : Operand 64).read u15) = a.l3 := (e15.agrees.read (by simp [movR64M64Effect_components])).trans g14r9
  have g16r9 : ((Operand.reg 9 : Operand 64).read u16) = a.l3 := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r9
  have g17r9 : ((Operand.reg 9 : Operand 64).read u17) = a.l3 := (e17.agrees.read (by simp [addR64R64Effect_components])).trans g16r9
  have g18r9 : ((Operand.reg 9 : Operand 64).read u18) = a.l3 := (e18.agrees.read (by simp [adcR64R64Effect_components])).trans g17r9
  have g19r9 : ((Operand.reg 9 : Operand 64).read u19) = a.l3 := (e19.agrees.read (by simp [movR64M64Effect_components])).trans g18r9
  have g20r9 : ((Operand.reg 9 : Operand 64).read u20) = a.l3 := (e20.agrees.read (by simp [mulR64Effect_components])).trans g19r9
  have g21r9 : ((Operand.reg 9 : Operand 64).read u21) = a.l3 := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r9
  have g11r10 : ((Operand.reg 10 : Operand 64).read u11) = a.l0 := (e11.agrees.read (by simp [addR64R64Effect_components])).trans g10r10
  have g12r10 : ((Operand.reg 10 : Operand 64).read u12) = a.l0 := (e12.agrees.read (by simp [adcR64R64Effect_components])).trans g11r10
  have g13r10 : ((Operand.reg 10 : Operand 64).read u13) = a.l0 := (e13.agrees.read (by simp [setccR8Effect_components])).trans g12r10
  have g14r10 : ((Operand.reg 10 : Operand 64).read u14) = a.l0 := (e14.agrees.read (by simp [movzxR32R8Effect_components])).trans g13r10
  have g15r10 : ((Operand.reg 10 : Operand 64).read u15) = a.l0 := (e15.agrees.read (by simp [movR64M64Effect_components])).trans g14r10
  have g16r10 : ((Operand.reg 10 : Operand 64).read u16) = a.l0 := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r10
  have g17r10 : ((Operand.reg 10 : Operand 64).read u17) = a.l0 := (e17.agrees.read (by simp [addR64R64Effect_components])).trans g16r10
  have g18r10 : ((Operand.reg 10 : Operand 64).read u18) = a.l0 := (e18.agrees.read (by simp [adcR64R64Effect_components])).trans g17r10
  have g19r10 : ((Operand.reg 10 : Operand 64).read u19) = a.l0 := (e19.agrees.read (by simp [movR64M64Effect_components])).trans g18r10
  have g20r10 : ((Operand.reg 10 : Operand 64).read u20) = a.l0 := (e20.agrees.read (by simp [mulR64Effect_components])).trans g19r10
  have g21r10 : ((Operand.reg 10 : Operand 64).read u21) = a.l0 := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r10
  have g1r13 : ((Operand.reg 13 : Operand 64).read u1) = a.l2 := (e1.agrees.read (by simp [movR64M64Effect_components])).trans g0r13
  have g2r13 : ((Operand.reg 13 : Operand 64).read u2) = a.l2 := (e2.agrees.read (by simp [imulR64R64Effect_components])).trans g1r13
  have g3r13 : ((Operand.reg 13 : Operand 64).read u3) = a.l2 := (e3.agrees.read (by simp [movR64R64Effect_components])).trans g2r13
  have g4r13 : ((Operand.reg 13 : Operand 64).read u4) = a.l2 := (e4.agrees.read (by simp [movR64M64Effect_components])).trans g3r13
  have g5r13 : ((Operand.reg 13 : Operand 64).read u5) = a.l2 := (e5.agrees.read (by simp [mulR64Effect_components])).trans g4r13
  have g6r13 : ((Operand.reg 13 : Operand 64).read u6) = a.l2 := (e6.agrees.read (by simp [movR64R64Effect_components])).trans g5r13
  have g7r13 : ((Operand.reg 13 : Operand 64).read u7) = a.l2 := (e7.agrees.read (by simp [movR64R64Effect_components])).trans g6r13
  have g8r13 : ((Operand.reg 13 : Operand 64).read u8) = a.l2 := (e8.agrees.read (by simp [movR64R64Effect_components])).trans g7r13
  have g9r13 : ((Operand.reg 13 : Operand 64).read u9) = a.l2 := (e9.agrees.read (by simp [mulR64Effect_components])).trans g8r13
  have g10r13 : ((Operand.reg 13 : Operand 64).read u10) = a.l2 := (e10.agrees.read (by simp [movR64R64Effect_components])).trans g9r13
  have g11r13 : ((Operand.reg 13 : Operand 64).read u11) = a.l2 := (e11.agrees.read (by simp [addR64R64Effect_components])).trans g10r13
  have g12r13 : ((Operand.reg 13 : Operand 64).read u12) = a.l2 := (e12.agrees.read (by simp [adcR64R64Effect_components])).trans g11r13
  have g13r13 : ((Operand.reg 13 : Operand 64).read u13) = a.l2 := (e13.agrees.read (by simp [setccR8Effect_components])).trans g12r13
  have g14r13 : ((Operand.reg 13 : Operand 64).read u14) = a.l2 := (e14.agrees.read (by simp [movzxR32R8Effect_components])).trans g13r13
  have g15r13 : ((Operand.reg 13 : Operand 64).read u15) = a.l2 := (e15.agrees.read (by simp [movR64M64Effect_components])).trans g14r13
  have g16r13 : ((Operand.reg 13 : Operand 64).read u16) = a.l2 := (e16.agrees.read (by simp [movR64M64Effect_components])).trans g15r13
  have g17r13 : ((Operand.reg 13 : Operand 64).read u17) = a.l2 := (e17.agrees.read (by simp [addR64R64Effect_components])).trans g16r13
  have g18r13 : ((Operand.reg 13 : Operand 64).read u18) = a.l2 := (e18.agrees.read (by simp [adcR64R64Effect_components])).trans g17r13
  have g19r13 : ((Operand.reg 13 : Operand 64).read u19) = a.l2 := (e19.agrees.read (by simp [movR64M64Effect_components])).trans g18r13
  have g20r13 : ((Operand.reg 13 : Operand 64).read u20) = a.l2 := (e20.agrees.read (by simp [mulR64Effect_components])).trans g19r13
  have g21r13 : ((Operand.reg 13 : Operand 64).read u21) = a.l2 := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r13
  have g17r14 : ((Operand.reg 14 : Operand 64).read u17) = extra := (e17.agrees.read (by simp [addR64R64Effect_components])).trans g16r14
  have g18r14 : ((Operand.reg 14 : Operand 64).read u18) = extra := (e18.agrees.read (by simp [adcR64R64Effect_components])).trans g17r14
  have g19r14 : ((Operand.reg 14 : Operand 64).read u19) = extra := (e19.agrees.read (by simp [movR64M64Effect_components])).trans g18r14
  have g20r14 : ((Operand.reg 14 : Operand 64).read u20) = extra := (e20.agrees.read (by simp [mulR64Effect_components])).trans g19r14
  have g21r14 : ((Operand.reg 14 : Operand 64).read u21) = extra := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r14
  have g21r0 : ((Operand.reg 0 : Operand 64).read u21) = 0 := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r0
  have g21r2 : ((Operand.reg 2 : Operand 64).read u21) = 0 := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r2
  have g18r3 : ((Operand.reg 3 : Operand 64).read u18) = x.1 := (e18.agrees.read (by simp [adcR64R64Effect_components])).trans g17r3
  have g19r3 : ((Operand.reg 3 : Operand 64).read u19) = x.1 := (e19.agrees.read (by simp [movR64M64Effect_components])).trans g18r3
  have g20r3 : ((Operand.reg 3 : Operand 64).read u20) = x.1 := (e20.agrees.read (by simp [mulR64Effect_components])).trans g19r3
  have g21r3 : ((Operand.reg 3 : Operand 64).read u21) = x.1 := (e21.agrees.read (by simp [xorR32R32Effect_components])).trans g20r3
  exact ⟨u21, ((((((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17).trans run18).trans run19).trans run20).trans run21), f21, e21.rip, mem21, g21r7, g21r11, g21r6, g21r5, g21r1, g21r9, g21r10, g21r13, g21r14, g21r0, g21r2, g21r8, g21r3⟩


end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.FourthRound
