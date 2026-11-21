import P256.Proofs.Projective.Double.Values
import P256.Proofs.Projective.Double.Output.CopyState
import P256.Proofs.Projective.Double.Output.YCopy
import P256.Proofs.Projective.Double.Output.ZCopy
import P256.Proofs.Projective.Double.Output.YZCopy
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Field.Double
import P256.Proofs.Field.Montgomery
import P256.Proofs.Field.Subtract
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false


namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Output

structure Output.YZProductsAt (s t : RamState) (point : Projective) : Prop where
  rbx : t.regValue .rbx = s.regValue .rdi
  r14 : t.regValue .r14 = stackPtr s - 304
  r12 : t.regValue .r12 = stackPtr s - 688
  r15 : t.regValue .r15 = stackPtr s - 240
  yy : MontgomeryAt t (stackPtr s - 592) (values point).yy
  xProduct : MontgomeryAt t (stackPtr s - 208) (values point).xProduct
  y : MontgomeryAt t (stackPtr s - 272) (values point).output.y
  yz2 : MontgomeryAt t (stackPtr s - 240) (values point).yz2
  product : MontgomeryAt t (stackPtr s - 688) ((values point).bxz6 * (values point).yz2 % Operations.domain.p)

set_option maxRecDepth 1024 in
theorem Output.prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x10635a)
    (input : CombinationsAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x106415 ∧ YZProductsAt s u point := by
  have cp1 := point_copy_pre pre state (source := 32) (target := 40) rip input.rbx (by decide) (by decide)
  obtain ⟨n1, t1, run1, ready1, _, effect1⟩ := YCopy.correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x635a YCopy.codeBytes
      (by decide +kernel) (by decide +kernel)) cp1
  have frame1 := copy_frame pre state ready1 effect1 (by decide)
  have copied1 := copy_montgomery cp1 effect1 (by change MontgomeryAt t (t.regValue .rbx + 32) point.y; rw [input.rbx]; exact input.pointAt.2.1)
  rw [scalar_stack_address (frameOffset := 728) state.rsp (by decide) (offset := 40) (by decide)] at copied1
  have r1_rbx : t1.regValue .rbx = s.regValue .rdi :=
    (effect1.agrees.read (n := 64) (r := 3) (by simp [copyEffect, Copy32.effect, Effect.components])).trans input.rbx
  have r1_r14 : t1.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect1.agrees.read (n := 64) (r := 14) (by simp [copyEffect, Copy32.effect, Effect.components])).trans input.r14
  have m1_592 := copy_keeps state effect1 (offset := 592) (by decide) (by decide) (by decide) (by decide) input.yy
  have m1_304 := copy_keeps state effect1 (offset := 304) (by decide) (by decide) (by decide) (by decide) input.bxz6
  have m1_208 := copy_keeps state effect1 (offset := 208) (by decide) (by decide) (by decide) (by decide) input.xProduct
  have m1_272 := copy_keeps state effect1 (offset := 272) (by decide) (by decide) (by decide) (by decide) input.y
  have point1 := point_of_stack pre (copy_stack_frame pre state effect1 (by decide)) input.pointAt
  have cp2 := point_copy_pre pre frame1 (source := 64) (target := 8) effect1.rip r1_rbx (by decide) (by decide)
  obtain ⟨n2, t2, run2, ready2, _, effect2⟩ := ZCopy.correct boundary pre.outerBoundary t1
    (readyToStep frame1.machine frame1.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame1.loaded) 0x637e ZCopy.codeBytes
      (by decide +kernel) (by decide +kernel)) cp2
  have frame2 := copy_frame pre frame1 ready2 effect2 (by decide)
  have copied2 := copy_montgomery cp2 effect2 (by change MontgomeryAt t1 (t1.regValue .rbx + 64) point.z; rw [r1_rbx]; exact point1.2.2)
  rw [scalar_stack_address (frameOffset := 728) frame1.rsp (by decide) (offset := 8) (by decide)] at copied2
  have r2_rbx : t2.regValue .rbx = s.regValue .rdi :=
    (effect2.agrees.read (n := 64) (r := 3) (by simp [copyEffect, Copy32.effect, Effect.components])).trans r1_rbx
  have r2_r14 : t2.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect2.agrees.read (n := 64) (r := 14) (by simp [copyEffect, Copy32.effect, Effect.components])).trans r1_r14
  have m2_592 := copy_keeps frame1 effect2 (offset := 592) (by decide) (by decide) (by decide) (by decide) m1_592
  have m2_304 := copy_keeps frame1 effect2 (offset := 304) (by decide) (by decide) (by decide) (by decide) m1_304
  have m2_208 := copy_keeps frame1 effect2 (offset := 208) (by decide) (by decide) (by decide) (by decide) m1_208
  have m2_272 := copy_keeps frame1 effect2 (offset := 272) (by decide) (by decide) (by decide) (by decide) m1_272
  have m2_688 := copy_keeps frame1 effect2 (offset := 688) (by decide) (by decide) (by decide) (by decide) copied1
  obtain ⟨t3, run3, frame3, effect3⟩ := step_registers pre frame2
    (offset := 0x63a2) (lea_r64_effect_step 0x1063a2 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect2.rip
    (inProgram_of_textOffset 0x63a7 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 12, .rip]; decide +kernel)
  have r3_r12 : t3.regValue .r12 = stackPtr s - BitVec.ofNat 64 656 := by
    have hw : t3.regValue .r12 = stackPtr t2 + 72 := effect3.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame2.rsp (by decide) (offset := 72) (by decide))
  have r3_rbx : t3.regValue .rbx = s.regValue .rdi :=
    (effect3.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 12, .rip]; decide +kernel)).trans r2_rbx
  have r3_r14 : t3.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect3.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 12, .rip]; decide +kernel)).trans r2_r14
  obtain ⟨t4, run4, frame4, effect4⟩ := step_registers pre frame3
    (offset := 0x63a7) (lea_r64_effect_step 0x1063a7 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect3.rip
    (inProgram_of_textOffset 0x63ac (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have r4_rsi : t4.regValue .rsi = stackPtr s - BitVec.ofNat 64 688 := by
    have hw : t4.regValue .rsi = stackPtr t3 + 40 := effect4.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame3.rsp (by decide) (offset := 40) (by decide))
  have r4_rbx : t4.regValue .rbx = s.regValue .rdi :=
    (effect4.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r3_rbx
  have r4_r14 : t4.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect4.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r3_r14
  have r4_r12 : t4.regValue .r12 = stackPtr s - BitVec.ofNat 64 656 :=
    (effect4.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r3_r12
  obtain ⟨t5, run5, frame5, effect5⟩ := step_registers pre frame4
    (offset := 0x63ac) (lea_r64_effect_step 0x1063ac 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect4.rip
    (inProgram_of_textOffset 0x63b1 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 2, .rip]; decide +kernel)
  have r5_rdx : t5.regValue .rdx = stackPtr s - BitVec.ofNat 64 720 := by
    have hw : t5.regValue .rdx = stackPtr t4 + 8 := effect5.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame4.rsp (by decide) (offset := 8) (by decide))
  have r5_rbx : t5.regValue .rbx = s.regValue .rdi :=
    (effect5.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r4_rbx
  have r5_r14 : t5.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect5.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r4_r14
  have r5_r12 : t5.regValue .r12 = stackPtr s - BitVec.ofNat 64 656 :=
    (effect5.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r4_r12
  have r5_rsi : t5.regValue .rsi = stackPtr s - BitVec.ofNat 64 688 :=
    (effect5.agrees.read (n := 64) (r := 6) (by change Component.reg 6 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r4_rsi
  obtain ⟨t6, run6, frame6, effect6⟩ := step_registers pre frame5
    (offset := 0x63b1) (mov_r64_r64_effect_step 0x1063b1 0x4c 0xe7 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect5.rip
    (inProgram_of_textOffset 0x63b4 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have r6_rdi : t6.regValue .rdi = stackPtr s - BitVec.ofNat 64 656 := by
    have hw : t6.regValue .rdi = t5.regValue .r12 := effect6.writes
    exact hw.trans r5_r12
  have r6_rbx : t6.regValue .rbx = s.regValue .rdi :=
    (effect6.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r5_rbx
  have r6_r14 : t6.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect6.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r5_r14
  have r6_r12 : t6.regValue .r12 = stackPtr s - BitVec.ofNat 64 656 :=
    (effect6.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r5_r12
  have r6_rsi : t6.regValue .rsi = stackPtr s - BitVec.ofNat 64 688 :=
    (effect6.agrees.read (n := 64) (r := 6) (by change Component.reg 6 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r5_rsi
  have r6_rdx : t6.regValue .rdx = stackPtr s - BitVec.ofNat 64 720 :=
    (effect6.agrees.read (n := 64) (r := 2) (by change Component.reg 2 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r5_rdx
  have ext6 : t6.external = t2.external := (((effect3.agrees.trans effect4.agrees).trans effect5.agrees).trans effect6.agrees).external (by simp [Component.Covers])
  have m6_592 : MontgomeryAt t6 (stackPtr s - BitVec.ofNat 64 592) (values point).yy := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using m2_592
  have m6_304 : MontgomeryAt t6 (stackPtr s - BitVec.ofNat 64 304) (values point).bxz6 := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using m2_304
  have m6_208 : MontgomeryAt t6 (stackPtr s - BitVec.ofNat 64 208) (values point).xProduct := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using m2_208
  have m6_272 : MontgomeryAt t6 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using m2_272
  have m6_688 : MontgomeryAt t6 (stackPtr s - BitVec.ofNat 64 688) point.y := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using m2_688
  have m6_720 : MontgomeryAt t6 (stackPtr s - BitVec.ofNat 64 720) point.z := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using copied2
  obtain ⟨n7, t7, run7, frame7, rip7, value7, regs7, bytes7, _⟩ :=
    binary_call pre frame6 (op := fun x y => x*y % P256.Spec.Operations.domain.p)
      (⟨0x63b4, 0xd4d7, by decide, by decide +kernel, by decide, by decide,
        inProgram_of_textOffset 0x13890 (by decide),
        ⟨736, 688, 656, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, rfl, by decide, 720, by decide, by decide, by decide⟩ : BinaryCallSite 1016 728 0x113890 280)
      (fun _ hp hx hy => field_mul_correct hp hx hy)
      effect6.rip r6_rsi r6_rdx r6_rdi m6_688 m6_720
  have r7_rbx : t7.regValue .rbx = s.regValue .rdi := (regs7 .rbx (by decide)).trans r6_rbx
  have r7_r14 : t7.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 := (regs7 .r14 (by decide)).trans r6_r14
  have r7_r12 : t7.regValue .r12 = stackPtr s - BitVec.ofNat 64 656 := (regs7 .r12 (by decide)).trans r6_r12
  have m7_592 : MontgomeryAt t7 (stackPtr s - BitVec.ofNat 64 592) (values point).yy :=
    ⟨m6_592.1, m6_592.2.1, fun i hi => (bytes7 592 32 (by decide) (by decide) (by decide) i hi).trans (m6_592.2.2 i hi)⟩
  have m7_304 : MontgomeryAt t7 (stackPtr s - BitVec.ofNat 64 304) (values point).bxz6 :=
    ⟨m6_304.1, m6_304.2.1, fun i hi => (bytes7 304 32 (by decide) (by decide) (by decide) i hi).trans (m6_304.2.2 i hi)⟩
  have m7_208 : MontgomeryAt t7 (stackPtr s - BitVec.ofNat 64 208) (values point).xProduct :=
    ⟨m6_208.1, m6_208.2.1, fun i hi => (bytes7 208 32 (by decide) (by decide) (by decide) i hi).trans (m6_208.2.2 i hi)⟩
  have m7_272 : MontgomeryAt t7 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y :=
    ⟨m6_272.1, m6_272.2.1, fun i hi => (bytes7 272 32 (by decide) (by decide) (by decide) i hi).trans (m6_272.2.2 i hi)⟩
  have m7_688 : MontgomeryAt t7 (stackPtr s - BitVec.ofNat 64 688) point.y :=
    ⟨m6_688.1, m6_688.2.1, fun i hi => (bytes7 688 32 (by decide) (by decide) (by decide) i hi).trans (m6_688.2.2 i hi)⟩
  have m7_720 : MontgomeryAt t7 (stackPtr s - BitVec.ofNat 64 720) point.z :=
    ⟨m6_720.1, m6_720.2.1, fun i hi => (bytes7 720 32 (by decide) (by decide) (by decide) i hi).trans (m6_720.2.2 i hi)⟩
  obtain ⟨t8, run8, frame8, effect8⟩ := step_registers pre frame7
    (offset := 0x63b9) (lea_r64_effect_step 0x1063b9 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 488)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) rip7
    (inProgram_of_textOffset 0x63c1 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 15, .rip]; decide +kernel)
  have r8_r15 : t8.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 := by
    have hw : t8.regValue .r15 = stackPtr t7 + 488 := effect8.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame7.rsp (by decide) (offset := 488) (by decide))
  have r8_rbx : t8.regValue .rbx = s.regValue .rdi :=
    (effect8.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 15, .rip]; decide +kernel)).trans r7_rbx
  have r8_r14 : t8.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect8.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 15, .rip]; decide +kernel)).trans r7_r14
  have r8_r12 : t8.regValue .r12 = stackPtr s - BitVec.ofNat 64 656 :=
    (effect8.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 15, .rip]; decide +kernel)).trans r7_r12
  obtain ⟨t9, run9, frame9, effect9⟩ := step_registers pre frame8
    (offset := 0x63c1) (mov_r64_r64_effect_step 0x1063c1 0x4c 0xff (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect8.rip
    (inProgram_of_textOffset 0x63c4 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have r9_rdi : t9.regValue .rdi = stackPtr s - BitVec.ofNat 64 240 := by
    have hw : t9.regValue .rdi = t8.regValue .r15 := effect9.writes
    exact hw.trans r8_r15
  have r9_rbx : t9.regValue .rbx = s.regValue .rdi :=
    (effect9.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r8_rbx
  have r9_r14 : t9.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect9.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r8_r14
  have r9_r12 : t9.regValue .r12 = stackPtr s - BitVec.ofNat 64 656 :=
    (effect9.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r8_r12
  have r9_r15 : t9.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect9.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r8_r15
  obtain ⟨t10, run10, frame10, effect10⟩ := step_registers pre frame9
    (offset := 0x63c4) (mov_r64_r64_effect_step 0x1063c4 0x4c 0xe6 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect9.rip
    (inProgram_of_textOffset 0x63c7 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have r10_rsi : t10.regValue .rsi = stackPtr s - BitVec.ofNat 64 656 := by
    have hw : t10.regValue .rsi = t9.regValue .r12 := effect10.writes
    exact hw.trans r9_r12
  have r10_rbx : t10.regValue .rbx = s.regValue .rdi :=
    (effect10.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r9_rbx
  have r10_r14 : t10.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect10.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r9_r14
  have r10_r12 : t10.regValue .r12 = stackPtr s - BitVec.ofNat 64 656 :=
    (effect10.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r9_r12
  have r10_r15 : t10.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect10.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r9_r15
  have r10_rdi : t10.regValue .rdi = stackPtr s - BitVec.ofNat 64 240 :=
    (effect10.agrees.read (n := 64) (r := 7) (by change Component.reg 7 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r9_rdi
  have ext10 : t10.external = t7.external := ((effect8.agrees.trans effect9.agrees).trans effect10.agrees).external (by simp [Component.Covers])
  have m10_592 : MontgomeryAt t10 (stackPtr s - BitVec.ofNat 64 592) (values point).yy := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using m7_592
  have m10_304 : MontgomeryAt t10 (stackPtr s - BitVec.ofNat 64 304) (values point).bxz6 := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using m7_304
  have m10_208 : MontgomeryAt t10 (stackPtr s - BitVec.ofNat 64 208) (values point).xProduct := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using m7_208
  have m10_272 : MontgomeryAt t10 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using m7_272
  have m10_656 : MontgomeryAt t10 (stackPtr s - BitVec.ofNat 64 656) (point.y * point.z % P256.Spec.Operations.domain.p) := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using value7
  obtain ⟨n11, t11, run11, frame11, rip11, value11, regs11, bytes11, _⟩ :=
    unary_call pre frame10 (entry := 0x1137f0) (reserve := 16) (outputBytes := 32)
      (resultAt := fun v a => MontgomeryAt v a (((point.y * point.z % P256.Spec.Operations.domain.p) + (point.y * point.z % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p))
      ⟨736, 656, 240, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ rfl (by decide) 0x63c7 0xd424
      (by decide) (by decide +kernel) (by decide) (by decide)
      (inProgram_of_textOffset 0x137f0 (by decide))
      (fun _ hp hx => field_double_correct hp hx)
      effect10.rip r10_rsi r10_rdi m10_656
  have r11_rbx : t11.regValue .rbx = s.regValue .rdi := (regs11 .rbx (by decide)).trans r10_rbx
  have r11_r14 : t11.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 := (regs11 .r14 (by decide)).trans r10_r14
  have r11_r12 : t11.regValue .r12 = stackPtr s - BitVec.ofNat 64 656 := (regs11 .r12 (by decide)).trans r10_r12
  have r11_r15 : t11.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 := (regs11 .r15 (by decide)).trans r10_r15
  have m11_592 : MontgomeryAt t11 (stackPtr s - BitVec.ofNat 64 592) (values point).yy :=
    ⟨m10_592.1, m10_592.2.1, fun i hi => (bytes11 592 32 (by decide) (by decide) (by decide) i hi).trans (m10_592.2.2 i hi)⟩
  have m11_304 : MontgomeryAt t11 (stackPtr s - BitVec.ofNat 64 304) (values point).bxz6 :=
    ⟨m10_304.1, m10_304.2.1, fun i hi => (bytes11 304 32 (by decide) (by decide) (by decide) i hi).trans (m10_304.2.2 i hi)⟩
  have m11_208 : MontgomeryAt t11 (stackPtr s - BitVec.ofNat 64 208) (values point).xProduct :=
    ⟨m10_208.1, m10_208.2.1, fun i hi => (bytes11 208 32 (by decide) (by decide) (by decide) i hi).trans (m10_208.2.2 i hi)⟩
  have m11_272 : MontgomeryAt t11 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y :=
    ⟨m10_272.1, m10_272.2.1, fun i hi => (bytes11 272 32 (by decide) (by decide) (by decide) i hi).trans (m10_272.2.2 i hi)⟩
  have m11_656 : MontgomeryAt t11 (stackPtr s - BitVec.ofNat 64 656) (point.y * point.z % P256.Spec.Operations.domain.p) :=
    ⟨m10_656.1, m10_656.2.1, fun i hi => (bytes11 656 32 (by decide) (by decide) (by decide) i hi).trans (m10_656.2.2 i hi)⟩
  have yz11 : MontgomeryAt t11 (stackPtr s - BitVec.ofNat 64 240) (values point).yz2 := value11
  have cp12 := stack_copy_pre pre frame11 (source := 488) (target := 8) rip11 (by decide) (by decide) (by decide)
  obtain ⟨n12, t12, run12, ready12, _, effect12⟩ := YZCopy.correct boundary pre.outerBoundary t11
    (readyToStep frame11.machine frame11.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame11.loaded) 0x63cc YZCopy.codeBytes
      (by decide +kernel) (by decide +kernel)) cp12
  have frame12 := copy_frame pre frame11 ready12 effect12 (by decide)
  have copied12 := copy_montgomery cp12 effect12 (by change MontgomeryAt t11 (stackPtr t11 + BitVec.ofNat 64 488) (values point).yz2; rw [scalar_stack_address (frameOffset := 728) frame11.rsp (by decide) (offset := 488) (by decide)]; exact yz11)
  rw [scalar_stack_address (frameOffset := 728) frame11.rsp (by decide) (offset := 8) (by decide)] at copied12
  have r12_rbx : t12.regValue .rbx = s.regValue .rdi :=
    (effect12.agrees.read (n := 64) (r := 3) (by simp [copyEffect, Copy32.effect, Effect.components])).trans r11_rbx
  have r12_r14 : t12.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect12.agrees.read (n := 64) (r := 14) (by simp [copyEffect, Copy32.effect, Effect.components])).trans r11_r14
  have r12_r12 : t12.regValue .r12 = stackPtr s - BitVec.ofNat 64 656 :=
    (effect12.agrees.read (n := 64) (r := 12) (by simp [copyEffect, Copy32.effect, Effect.components])).trans r11_r12
  have r12_r15 : t12.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect12.agrees.read (n := 64) (r := 15) (by simp [copyEffect, Copy32.effect, Effect.components])).trans r11_r15
  have m12_592 := copy_keeps frame11 effect12 (offset := 592) (by decide) (by decide) (by decide) (by decide) m11_592
  have m12_304 := copy_keeps frame11 effect12 (offset := 304) (by decide) (by decide) (by decide) (by decide) m11_304
  have m12_208 := copy_keeps frame11 effect12 (offset := 208) (by decide) (by decide) (by decide) (by decide) m11_208
  have m12_272 := copy_keeps frame11 effect12 (offset := 272) (by decide) (by decide) (by decide) (by decide) m11_272
  have m12_240 := copy_keeps frame11 effect12 (offset := 240) (by decide) (by decide) (by decide) (by decide) yz11
  obtain ⟨t13, run13, frame13, effect13⟩ := step_registers pre frame12
    (offset := 0x6400) (lea_r64_effect_step 0x106400 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect12.rip
    (inProgram_of_textOffset 0x6405 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 12, .rip]; decide +kernel)
  have r13_r12 : t13.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 := by
    have hw : t13.regValue .r12 = stackPtr t12 + 40 := effect13.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame12.rsp (by decide) (offset := 40) (by decide))
  have r13_rbx : t13.regValue .rbx = s.regValue .rdi :=
    (effect13.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 12, .rip]; decide +kernel)).trans r12_rbx
  have r13_r14 : t13.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect13.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 12, .rip]; decide +kernel)).trans r12_r14
  have r13_r15 : t13.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect13.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 12, .rip]; decide +kernel)).trans r12_r15
  obtain ⟨t14, run14, frame14, effect14⟩ := step_registers pre frame13
    (offset := 0x6405) (lea_r64_effect_step 0x106405 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect13.rip
    (inProgram_of_textOffset 0x640a (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 2, .rip]; decide +kernel)
  have r14_rdx : t14.regValue .rdx = stackPtr s - BitVec.ofNat 64 720 := by
    have hw : t14.regValue .rdx = stackPtr t13 + 8 := effect14.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame13.rsp (by decide) (offset := 8) (by decide))
  have r14_rbx : t14.regValue .rbx = s.regValue .rdi :=
    (effect14.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r13_rbx
  have r14_r14 : t14.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect14.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r13_r14
  have r14_r12 : t14.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect14.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r13_r12
  have r14_r15 : t14.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect14.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r13_r15
  obtain ⟨t15, run15, frame15, effect15⟩ := step_registers pre frame14
    (offset := 0x640a) (mov_r64_r64_effect_step 0x10640a 0x4c 0xe7 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect14.rip
    (inProgram_of_textOffset 0x640d (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have r15_rdi : t15.regValue .rdi = stackPtr s - BitVec.ofNat 64 688 := by
    have hw : t15.regValue .rdi = t14.regValue .r12 := effect15.writes
    exact hw.trans r14_r12
  have r15_rbx : t15.regValue .rbx = s.regValue .rdi :=
    (effect15.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r14_rbx
  have r15_r14 : t15.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect15.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r14_r14
  have r15_r12 : t15.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect15.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r14_r12
  have r15_r15 : t15.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect15.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r14_r15
  have r15_rdx : t15.regValue .rdx = stackPtr s - BitVec.ofNat 64 720 :=
    (effect15.agrees.read (n := 64) (r := 2) (by change Component.reg 2 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r14_rdx
  obtain ⟨t16, run16, frame16, effect16⟩ := step_registers pre frame15
    (offset := 0x640d) (mov_r64_r64_effect_step 0x10640d 0x4c 0xf6 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect15.rip
    (inProgram_of_textOffset 0x6410 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have r16_rsi : t16.regValue .rsi = stackPtr s - BitVec.ofNat 64 304 := by
    have hw : t16.regValue .rsi = t15.regValue .r14 := effect16.writes
    exact hw.trans r15_r14
  have r16_rbx : t16.regValue .rbx = s.regValue .rdi :=
    (effect16.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r15_rbx
  have r16_r14 : t16.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect16.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r15_r14
  have r16_r12 : t16.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect16.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r15_r12
  have r16_r15 : t16.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect16.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r15_r15
  have r16_rdx : t16.regValue .rdx = stackPtr s - BitVec.ofNat 64 720 :=
    (effect16.agrees.read (n := 64) (r := 2) (by change Component.reg 2 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r15_rdx
  have r16_rdi : t16.regValue .rdi = stackPtr s - BitVec.ofNat 64 688 :=
    (effect16.agrees.read (n := 64) (r := 7) (by change Component.reg 7 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r15_rdi
  have ext16 : t16.external = t12.external := (((effect13.agrees.trans effect14.agrees).trans effect15.agrees).trans effect16.agrees).external (by simp [Component.Covers])
  have m16_592 : MontgomeryAt t16 (stackPtr s - BitVec.ofNat 64 592) (values point).yy := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using m12_592
  have m16_304 : MontgomeryAt t16 (stackPtr s - BitVec.ofNat 64 304) (values point).bxz6 := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using m12_304
  have m16_208 : MontgomeryAt t16 (stackPtr s - BitVec.ofNat 64 208) (values point).xProduct := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using m12_208
  have m16_272 : MontgomeryAt t16 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using m12_272
  have m16_240 : MontgomeryAt t16 (stackPtr s - BitVec.ofNat 64 240) (values point).yz2 := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using m12_240
  have m16_720 : MontgomeryAt t16 (stackPtr s - BitVec.ofNat 64 720) (values point).yz2 := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using copied12
  obtain ⟨n17, t17, run17, frame17, rip17, value17, regs17, bytes17, _⟩ :=
    binary_call pre frame16 (op := fun x y => x*y % P256.Spec.Operations.domain.p)
      (⟨0x6410, 0xd47b, by decide, by decide +kernel, by decide, by decide,
        inProgram_of_textOffset 0x13890 (by decide),
        ⟨736, 304, 688, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, rfl, by decide, 720, by decide, by decide, by decide⟩ : BinaryCallSite 1016 728 0x113890 280)
      (fun _ hp hx hy => field_mul_correct hp hx hy)
      effect16.rip r16_rsi r16_rdx r16_rdi m16_304 m16_720
  have r17_rbx : t17.regValue .rbx = s.regValue .rdi := (regs17 .rbx (by decide)).trans r16_rbx
  have r17_r14 : t17.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 := (regs17 .r14 (by decide)).trans r16_r14
  have r17_r12 : t17.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 := (regs17 .r12 (by decide)).trans r16_r12
  have r17_r15 : t17.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 := (regs17 .r15 (by decide)).trans r16_r15
  have m17_592 : MontgomeryAt t17 (stackPtr s - BitVec.ofNat 64 592) (values point).yy :=
    ⟨m16_592.1, m16_592.2.1, fun i hi => (bytes17 592 32 (by decide) (by decide) (by decide) i hi).trans (m16_592.2.2 i hi)⟩
  have m17_304 : MontgomeryAt t17 (stackPtr s - BitVec.ofNat 64 304) (values point).bxz6 :=
    ⟨m16_304.1, m16_304.2.1, fun i hi => (bytes17 304 32 (by decide) (by decide) (by decide) i hi).trans (m16_304.2.2 i hi)⟩
  have m17_208 : MontgomeryAt t17 (stackPtr s - BitVec.ofNat 64 208) (values point).xProduct :=
    ⟨m16_208.1, m16_208.2.1, fun i hi => (bytes17 208 32 (by decide) (by decide) (by decide) i hi).trans (m16_208.2.2 i hi)⟩
  have m17_272 : MontgomeryAt t17 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y :=
    ⟨m16_272.1, m16_272.2.1, fun i hi => (bytes17 272 32 (by decide) (by decide) (by decide) i hi).trans (m16_272.2.2 i hi)⟩
  have m17_240 : MontgomeryAt t17 (stackPtr s - BitVec.ofNat 64 240) (values point).yz2 :=
    ⟨m16_240.1, m16_240.2.1, fun i hi => (bytes17 240 32 (by decide) (by decide) (by decide) i hi).trans (m16_240.2.2 i hi)⟩
  have m17_720 : MontgomeryAt t17 (stackPtr s - BitVec.ofNat 64 720) (values point).yz2 :=
    ⟨m16_720.1, m16_720.2.1, fun i hi => (bytes17 720 32 (by decide) (by decide) (by decide) i hi).trans (m16_720.2.2 i hi)⟩
  exact ⟨_, t17, ((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17), frame17, rip17, r17_rbx, r17_r14, r17_r12, r17_r15, m17_592, m17_208, m17_272, m17_240, value17⟩

end P256.Proofs.Projective.Double
