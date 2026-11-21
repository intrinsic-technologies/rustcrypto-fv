import P256.Proofs.Projective.Double.Output.Prepare
set_option autoImplicit false


namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Output

set_option maxRecDepth 1024 in
theorem Output.finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x106415)
    (input : YZProductsAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x106462 ∧ OutputAt s u point := by
  have frame17 := state
  have rip17 := rip
  have r17_rbx := input.rbx
  have r17_r14 := input.r14
  have r17_r12 := input.r12
  have r17_r15 := input.r15
  have m17_592 := input.yy
  have m17_208 := input.xProduct
  have m17_272 := input.y
  have m17_240 := input.yz2
  have value17 := input.product
  obtain ⟨t18, run18, frame18, effect18⟩ := step_registers pre frame17
    (offset := 0x6415) (lea_r64_effect_step 0x106415 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 232)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) rip17
    (inProgram_of_textOffset 0x641d (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have r18_rdi : t18.regValue .rdi = stackPtr s - BitVec.ofNat 64 496 := by
    have hw : t18.regValue .rdi = stackPtr t + 232 := effect18.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame17.rsp (by decide) (offset := 232) (by decide))
  have r18_rbx : t18.regValue .rbx = s.regValue .rdi :=
    (effect18.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r17_rbx
  have r18_r14 : t18.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect18.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r17_r14
  have r18_r12 : t18.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect18.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r17_r12
  have r18_r15 : t18.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect18.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r17_r15
  obtain ⟨t19, run19, frame19, effect19⟩ := step_registers pre frame18
    (offset := 0x641d) (lea_r64_effect_step 0x10641d 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 520)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect18.rip
    (inProgram_of_textOffset 0x6425 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have r19_rsi : t19.regValue .rsi = stackPtr s - BitVec.ofNat 64 208 := by
    have hw : t19.regValue .rsi = stackPtr t18 + 520 := effect19.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame18.rsp (by decide) (offset := 520) (by decide))
  have r19_rbx : t19.regValue .rbx = s.regValue .rdi :=
    (effect19.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r18_rbx
  have r19_r14 : t19.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect19.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r18_r14
  have r19_r12 : t19.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect19.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r18_r12
  have r19_r15 : t19.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect19.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r18_r15
  have r19_rdi : t19.regValue .rdi = stackPtr s - BitVec.ofNat 64 496 :=
    (effect19.agrees.read (n := 64) (r := 7) (by change Component.reg 7 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r18_rdi
  obtain ⟨t20, run20, frame20, effect20⟩ := step_registers pre frame19
    (offset := 0x6425) (mov_r64_r64_effect_step 0x106425 0x4c 0xe2 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect19.rip
    (inProgram_of_textOffset 0x6428 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 2, .rip]; decide +kernel)
  have r20_rdx : t20.regValue .rdx = stackPtr s - BitVec.ofNat 64 688 := by
    have hw : t20.regValue .rdx = t19.regValue .r12 := effect20.writes
    exact hw.trans r19_r12
  have r20_rbx : t20.regValue .rbx = s.regValue .rdi :=
    (effect20.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r19_rbx
  have r20_r14 : t20.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 :=
    (effect20.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r19_r14
  have r20_r12 : t20.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect20.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r19_r12
  have r20_r15 : t20.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect20.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r19_r15
  have r20_rdi : t20.regValue .rdi = stackPtr s - BitVec.ofNat 64 496 :=
    (effect20.agrees.read (n := 64) (r := 7) (by change Component.reg 7 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r19_rdi
  have r20_rsi : t20.regValue .rsi = stackPtr s - BitVec.ofNat 64 208 :=
    (effect20.agrees.read (n := 64) (r := 6) (by change Component.reg 6 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r19_rsi
  have ext20 : t20.external = t.external := ((effect18.agrees.trans effect19.agrees).trans effect20.agrees).external (by simp [Component.Covers])
  have m20_592 : MontgomeryAt t20 (stackPtr s - BitVec.ofNat 64 592) (values point).yy := by
    exact m17_592.of_bytes_eq (fun i _ => by rw [ext20]; rfl)
  have m20_208 : MontgomeryAt t20 (stackPtr s - BitVec.ofNat 64 208) (values point).xProduct := by
    exact m17_208.of_bytes_eq (fun i _ => by rw [ext20]; rfl)
  have m20_272 : MontgomeryAt t20 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y := by
    exact m17_272.of_bytes_eq (fun i _ => by rw [ext20]; rfl)
  have m20_240 : MontgomeryAt t20 (stackPtr s - BitVec.ofNat 64 240) (values point).yz2 := by
    exact m17_240.of_bytes_eq (fun i _ => by rw [ext20]; rfl)
  have m20_688 : MontgomeryAt t20 (stackPtr s - BitVec.ofNat 64 688) ((values point).bxz6 * (values point).yz2 % P256.Spec.Operations.domain.p) := by
    exact value17.of_bytes_eq (fun i _ => by rw [ext20]; rfl)
  obtain ⟨n21, t21, run21, frame21, rip21, value21, regs21, bytes21, _⟩ :=
    binary_call pre frame20 (op := Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p)
      (⟨0x6428, 0xd3b3, by decide, by decide +kernel, by decide, by decide,
        inProgram_of_textOffset 0x137e0 (by decide),
        ⟨736, 208, 496, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, rfl, by decide, 688, by decide, by decide, by decide⟩ : BinaryCallSite 1016 728 0x1137e0 24)
      (fun _ hp hx hy => by simpa only [Standards.SECG.ECC.Curve.fieldSub, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] using field_subtract_correct hp hx hy)
      effect20.rip r20_rsi r20_rdx r20_rdi m20_208 m20_688
  have r21_rbx : t21.regValue .rbx = s.regValue .rdi := (regs21 .rbx (by decide)).trans r20_rbx
  have r21_r14 : t21.regValue .r14 = stackPtr s - BitVec.ofNat 64 304 := (regs21 .r14 (by decide)).trans r20_r14
  have r21_r12 : t21.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 := (regs21 .r12 (by decide)).trans r20_r12
  have r21_r15 : t21.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 := (regs21 .r15 (by decide)).trans r20_r15
  have m21_592 : MontgomeryAt t21 (stackPtr s - BitVec.ofNat 64 592) (values point).yy :=
    ⟨m20_592.1, m20_592.2.1, fun i hi => (bytes21 592 32 (by decide) (by decide) (by decide) i hi).trans (m20_592.2.2 i hi)⟩
  have m21_208 : MontgomeryAt t21 (stackPtr s - BitVec.ofNat 64 208) (values point).xProduct :=
    ⟨m20_208.1, m20_208.2.1, fun i hi => (bytes21 208 32 (by decide) (by decide) (by decide) i hi).trans (m20_208.2.2 i hi)⟩
  have m21_272 : MontgomeryAt t21 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y :=
    ⟨m20_272.1, m20_272.2.1, fun i hi => (bytes21 272 32 (by decide) (by decide) (by decide) i hi).trans (m20_272.2.2 i hi)⟩
  have m21_240 : MontgomeryAt t21 (stackPtr s - BitVec.ofNat 64 240) (values point).yz2 :=
    ⟨m20_240.1, m20_240.2.1, fun i hi => (bytes21 240 32 (by decide) (by decide) (by decide) i hi).trans (m20_240.2.2 i hi)⟩
  have m21_688 : MontgomeryAt t21 (stackPtr s - BitVec.ofNat 64 688) ((values point).bxz6 * (values point).yz2 % P256.Spec.Operations.domain.p) :=
    ⟨m20_688.1, m20_688.2.1, fun i hi => (bytes21 688 32 (by decide) (by decide) (by decide) i hi).trans (m20_688.2.2 i hi)⟩
  obtain ⟨t22, run22, frame22, effect22⟩ := step_registers pre frame21
    (offset := 0x642d) (lea_r64_effect_step 0x10642d 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) rip21
    (inProgram_of_textOffset 0x6432 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 14, .rip]; decide +kernel)
  have r22_r14 : t22.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 := by
    have hw : t22.regValue .r14 = stackPtr t21 + 8 := effect22.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame21.rsp (by decide) (offset := 8) (by decide))
  have r22_rbx : t22.regValue .rbx = s.regValue .rdi :=
    (effect22.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 14, .rip]; decide +kernel)).trans r21_rbx
  have r22_r12 : t22.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect22.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 14, .rip]; decide +kernel)).trans r21_r12
  have r22_r15 : t22.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect22.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 14, .rip]; decide +kernel)).trans r21_r15
  obtain ⟨t23, run23, frame23, effect23⟩ := step_registers pre frame22
    (offset := 0x6432) (mov_r64_r64_effect_step 0x106432 0x4c 0xf7 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect22.rip
    (inProgram_of_textOffset 0x6435 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have r23_rdi : t23.regValue .rdi = stackPtr s - BitVec.ofNat 64 720 := by
    have hw : t23.regValue .rdi = t22.regValue .r14 := effect23.writes
    exact hw.trans r22_r14
  have r23_rbx : t23.regValue .rbx = s.regValue .rdi :=
    (effect23.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r22_rbx
  have r23_r14 : t23.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 :=
    (effect23.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r22_r14
  have r23_r12 : t23.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect23.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r22_r12
  have r23_r15 : t23.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect23.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r22_r15
  obtain ⟨t24, run24, frame24, effect24⟩ := step_registers pre frame23
    (offset := 0x6435) (mov_r64_r64_effect_step 0x106435 0x4c 0xfe (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect23.rip
    (inProgram_of_textOffset 0x6438 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have r24_rsi : t24.regValue .rsi = stackPtr s - BitVec.ofNat 64 240 := by
    have hw : t24.regValue .rsi = t23.regValue .r15 := effect24.writes
    exact hw.trans r23_r15
  have r24_rbx : t24.regValue .rbx = s.regValue .rdi :=
    (effect24.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r23_rbx
  have r24_r14 : t24.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 :=
    (effect24.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r23_r14
  have r24_r12 : t24.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect24.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r23_r12
  have r24_r15 : t24.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect24.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r23_r15
  have r24_rdi : t24.regValue .rdi = stackPtr s - BitVec.ofNat 64 720 :=
    (effect24.agrees.read (n := 64) (r := 7) (by change Component.reg 7 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r23_rdi
  obtain ⟨t25, run25, frame25, effect25⟩ := step_registers pre frame24
    (offset := 0x6438) (lea_r64_effect_step 0x106438 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect24.rip
    (inProgram_of_textOffset 0x6440 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 2, .rip]; decide +kernel)
  have r25_rdx : t25.regValue .rdx = stackPtr s - BitVec.ofNat 64 592 := by
    have hw : t25.regValue .rdx = stackPtr t24 + 136 := effect25.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame24.rsp (by decide) (offset := 136) (by decide))
  have r25_rbx : t25.regValue .rbx = s.regValue .rdi :=
    (effect25.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r24_rbx
  have r25_r14 : t25.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 :=
    (effect25.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r24_r14
  have r25_r12 : t25.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect25.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r24_r12
  have r25_r15 : t25.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 :=
    (effect25.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r24_r15
  have r25_rdi : t25.regValue .rdi = stackPtr s - BitVec.ofNat 64 720 :=
    (effect25.agrees.read (n := 64) (r := 7) (by change Component.reg 7 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r24_rdi
  have r25_rsi : t25.regValue .rsi = stackPtr s - BitVec.ofNat 64 240 :=
    (effect25.agrees.read (n := 64) (r := 6) (by change Component.reg 6 ∉ [Component.reg 2, .rip]; decide +kernel)).trans r24_rsi
  have ext25 : t25.external = t21.external := (((effect22.agrees.trans effect23.agrees).trans effect24.agrees).trans effect25.agrees).external (by simp [Component.Covers])
  have m25_592 : MontgomeryAt t25 (stackPtr s - BitVec.ofNat 64 592) (values point).yy := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m21_592
  have m25_272 : MontgomeryAt t25 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m21_272
  have m25_240 : MontgomeryAt t25 (stackPtr s - BitVec.ofNat 64 240) (values point).yz2 := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m21_240
  have m25_496 : MontgomeryAt t25 (stackPtr s - BitVec.ofNat 64 496) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p (values point).xProduct ((values point).bxz6 * (values point).yz2 % P256.Spec.Operations.domain.p)) := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using value21
  obtain ⟨n26, t26, run26, frame26, rip26, value26, regs26, bytes26, _⟩ :=
    binary_call pre frame25 (op := fun x y => x*y % P256.Spec.Operations.domain.p)
      (⟨0x6440, 0xd44b, by decide, by decide +kernel, by decide, by decide,
        inProgram_of_textOffset 0x13890 (by decide),
        ⟨736, 240, 720, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, rfl, by decide, 592, by decide, by decide, by decide⟩ : BinaryCallSite 1016 728 0x113890 280)
      (fun _ hp hx hy => field_mul_correct hp hx hy)
      effect25.rip r25_rsi r25_rdx r25_rdi m25_240 m25_592
  have r26_rbx : t26.regValue .rbx = s.regValue .rdi := (regs26 .rbx (by decide)).trans r25_rbx
  have r26_r14 : t26.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 := (regs26 .r14 (by decide)).trans r25_r14
  have r26_r12 : t26.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 := (regs26 .r12 (by decide)).trans r25_r12
  have r26_r15 : t26.regValue .r15 = stackPtr s - BitVec.ofNat 64 240 := (regs26 .r15 (by decide)).trans r25_r15
  have m26_592 : MontgomeryAt t26 (stackPtr s - BitVec.ofNat 64 592) (values point).yy :=
    ⟨m25_592.1, m25_592.2.1, fun i hi => (bytes26 592 32 (by decide) (by decide) (by decide) i hi).trans (m25_592.2.2 i hi)⟩
  have m26_272 : MontgomeryAt t26 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y :=
    ⟨m25_272.1, m25_272.2.1, fun i hi => (bytes26 272 32 (by decide) (by decide) (by decide) i hi).trans (m25_272.2.2 i hi)⟩
  have m26_240 : MontgomeryAt t26 (stackPtr s - BitVec.ofNat 64 240) (values point).yz2 :=
    ⟨m25_240.1, m25_240.2.1, fun i hi => (bytes26 240 32 (by decide) (by decide) (by decide) i hi).trans (m25_240.2.2 i hi)⟩
  have m26_496 : MontgomeryAt t26 (stackPtr s - BitVec.ofNat 64 496) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p (values point).xProduct ((values point).bxz6 * (values point).yz2 % P256.Spec.Operations.domain.p)) :=
    ⟨m25_496.1, m25_496.2.1, fun i hi => (bytes26 496 32 (by decide) (by decide) (by decide) i hi).trans (m25_496.2.2 i hi)⟩
  obtain ⟨t27, run27, frame27, effect27⟩ := step_registers pre frame26
    (offset := 0x6445) (lea_r64_effect_step 0x106445 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) rip26
    (inProgram_of_textOffset 0x644a (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 15, .rip]; decide +kernel)
  have r27_r15 : t27.regValue .r15 = stackPtr s - BitVec.ofNat 64 688 := by
    have hw : t27.regValue .r15 = stackPtr t26 + 40 := effect27.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame26.rsp (by decide) (offset := 40) (by decide))
  have r27_rbx : t27.regValue .rbx = s.regValue .rdi :=
    (effect27.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 15, .rip]; decide +kernel)).trans r26_rbx
  have r27_r14 : t27.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 :=
    (effect27.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 15, .rip]; decide +kernel)).trans r26_r14
  have r27_r12 : t27.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect27.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 15, .rip]; decide +kernel)).trans r26_r12
  obtain ⟨t28, run28, frame28, effect28⟩ := step_registers pre frame27
    (offset := 0x644a) (mov_r64_r64_effect_step 0x10644a 0x4c 0xff (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect27.rip
    (inProgram_of_textOffset 0x644d (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have r28_rdi : t28.regValue .rdi = stackPtr s - BitVec.ofNat 64 688 := by
    have hw : t28.regValue .rdi = t27.regValue .r15 := effect28.writes
    exact hw.trans r27_r15
  have r28_rbx : t28.regValue .rbx = s.regValue .rdi :=
    (effect28.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r27_rbx
  have r28_r14 : t28.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 :=
    (effect28.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r27_r14
  have r28_r12 : t28.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect28.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r27_r12
  have r28_r15 : t28.regValue .r15 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect28.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r27_r15
  obtain ⟨t29, run29, frame29, effect29⟩ := step_registers pre frame28
    (offset := 0x644d) (mov_r64_r64_effect_step 0x10644d 0x4c 0xf6 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect28.rip
    (inProgram_of_textOffset 0x6450 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have r29_rsi : t29.regValue .rsi = stackPtr s - BitVec.ofNat 64 720 := by
    have hw : t29.regValue .rsi = t28.regValue .r14 := effect29.writes
    exact hw.trans r28_r14
  have r29_rbx : t29.regValue .rbx = s.regValue .rdi :=
    (effect29.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r28_rbx
  have r29_r14 : t29.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 :=
    (effect29.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r28_r14
  have r29_r12 : t29.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect29.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r28_r12
  have r29_r15 : t29.regValue .r15 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect29.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r28_r15
  have r29_rdi : t29.regValue .rdi = stackPtr s - BitVec.ofNat 64 688 :=
    (effect29.agrees.read (n := 64) (r := 7) (by change Component.reg 7 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r28_rdi
  have ext29 : t29.external = t26.external := ((effect27.agrees.trans effect28.agrees).trans effect29.agrees).external (by simp [Component.Covers])
  have m29_272 : MontgomeryAt t29 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext29] using m26_272
  have m29_496 : MontgomeryAt t29 (stackPtr s - BitVec.ofNat 64 496) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p (values point).xProduct ((values point).bxz6 * (values point).yz2 % P256.Spec.Operations.domain.p)) := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext29] using m26_496
  have m29_720 : MontgomeryAt t29 (stackPtr s - BitVec.ofNat 64 720) ((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p) := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext29] using value26
  obtain ⟨n30, t30, run30, frame30, rip30, value30, regs30, bytes30, _⟩ :=
    unary_call pre frame29 (entry := 0x1137f0) (reserve := 16) (outputBytes := 32)
      (resultAt := fun v a => MontgomeryAt v a ((((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p) + ((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p))
      ⟨736, 720, 688, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ rfl (by decide) 0x6450 0xd39b
      (by decide) (by decide +kernel) (by decide) (by decide)
      (inProgram_of_textOffset 0x137f0 (by decide))
      (fun _ hp hx => field_double_correct hp hx)
      effect29.rip r29_rsi r29_rdi m29_720
  have r30_rbx : t30.regValue .rbx = s.regValue .rdi := (regs30 .rbx (by decide)).trans r29_rbx
  have r30_r14 : t30.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 := (regs30 .r14 (by decide)).trans r29_r14
  have r30_r12 : t30.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 := (regs30 .r12 (by decide)).trans r29_r12
  have r30_r15 : t30.regValue .r15 = stackPtr s - BitVec.ofNat 64 688 := (regs30 .r15 (by decide)).trans r29_r15
  have m30_272 : MontgomeryAt t30 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y :=
    ⟨m29_272.1, m29_272.2.1, fun i hi => (bytes30 272 32 (by decide) (by decide) (by decide) i hi).trans (m29_272.2.2 i hi)⟩
  have m30_496 : MontgomeryAt t30 (stackPtr s - BitVec.ofNat 64 496) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p (values point).xProduct ((values point).bxz6 * (values point).yz2 % P256.Spec.Operations.domain.p)) :=
    ⟨m29_496.1, m29_496.2.1, fun i hi => (bytes30 496 32 (by decide) (by decide) (by decide) i hi).trans (m29_496.2.2 i hi)⟩
  have m30_720 : MontgomeryAt t30 (stackPtr s - BitVec.ofNat 64 720) ((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p) :=
    ⟨m29_720.1, m29_720.2.1, fun i hi => (bytes30 720 32 (by decide) (by decide) (by decide) i hi).trans (m29_720.2.2 i hi)⟩
  obtain ⟨t31, run31, frame31, effect31⟩ := step_registers pre frame30
    (offset := 0x6455) (lea_r64_effect_step 0x106455 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) rip30
    (inProgram_of_textOffset 0x645a (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have r31_rdi : t31.regValue .rdi = stackPtr s - BitVec.ofNat 64 656 := by
    have hw : t31.regValue .rdi = stackPtr t30 + 72 := effect31.writes
    exact hw.trans (scalar_stack_address (frameOffset := 728) frame30.rsp (by decide) (offset := 72) (by decide))
  have r31_rbx : t31.regValue .rbx = s.regValue .rdi :=
    (effect31.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r30_rbx
  have r31_r14 : t31.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 :=
    (effect31.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r30_r14
  have r31_r12 : t31.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect31.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r30_r12
  have r31_r15 : t31.regValue .r15 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect31.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 7, .rip]; decide +kernel)).trans r30_r15
  obtain ⟨t32, run32, frame32, effect32⟩ := step_registers pre frame31
    (offset := 0x645a) (mov_r64_r64_effect_step 0x10645a 0x4c 0xfe (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect31.rip
    (inProgram_of_textOffset 0x645d (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have r32_rsi : t32.regValue .rsi = stackPtr s - BitVec.ofNat 64 688 := by
    have hw : t32.regValue .rsi = t31.regValue .r15 := effect32.writes
    exact hw.trans r31_r15
  have r32_rbx : t32.regValue .rbx = s.regValue .rdi :=
    (effect32.agrees.read (n := 64) (r := 3) (by change Component.reg 3 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r31_rbx
  have r32_r14 : t32.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 :=
    (effect32.agrees.read (n := 64) (r := 14) (by change Component.reg 14 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r31_r14
  have r32_r12 : t32.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect32.agrees.read (n := 64) (r := 12) (by change Component.reg 12 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r31_r12
  have r32_r15 : t32.regValue .r15 = stackPtr s - BitVec.ofNat 64 688 :=
    (effect32.agrees.read (n := 64) (r := 15) (by change Component.reg 15 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r31_r15
  have r32_rdi : t32.regValue .rdi = stackPtr s - BitVec.ofNat 64 656 :=
    (effect32.agrees.read (n := 64) (r := 7) (by change Component.reg 7 ∉ [Component.reg 6, .rip]; decide +kernel)).trans r31_rdi
  have ext32 : t32.external = t30.external := (effect31.agrees.trans effect32.agrees).external (by simp [Component.Covers])
  have m32_272 : MontgomeryAt t32 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext32] using m30_272
  have m32_496 : MontgomeryAt t32 (stackPtr s - BitVec.ofNat 64 496) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p (values point).xProduct ((values point).bxz6 * (values point).yz2 % P256.Spec.Operations.domain.p)) := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext32] using m30_496
  have m32_688 : MontgomeryAt t32 (stackPtr s - BitVec.ofNat 64 688) ((((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p) + ((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p) := by
    simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext32] using value30
  obtain ⟨n33, t33, run33, frame33, rip33, value33, regs33, bytes33, _⟩ :=
    unary_call pre frame32 (entry := 0x1137f0) (reserve := 16) (outputBytes := 32)
      (resultAt := fun v a => MontgomeryAt v a ((((((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p) + ((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p) + ((((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p) + ((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p))
      ⟨736, 688, 656, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ rfl (by decide) 0x645d 0xd38e
      (by decide) (by decide +kernel) (by decide) (by decide)
      (inProgram_of_textOffset 0x137f0 (by decide))
      (fun _ hp hx => field_double_correct hp hx)
      effect32.rip r32_rsi r32_rdi m32_688
  have r33_rbx : t33.regValue .rbx = s.regValue .rdi := (regs33 .rbx (by decide)).trans r32_rbx
  have r33_r14 : t33.regValue .r14 = stackPtr s - BitVec.ofNat 64 720 := (regs33 .r14 (by decide)).trans r32_r14
  have r33_r12 : t33.regValue .r12 = stackPtr s - BitVec.ofNat 64 688 := (regs33 .r12 (by decide)).trans r32_r12
  have r33_r15 : t33.regValue .r15 = stackPtr s - BitVec.ofNat 64 688 := (regs33 .r15 (by decide)).trans r32_r15
  have m33_272 : MontgomeryAt t33 (stackPtr s - BitVec.ofNat 64 272) (values point).output.y :=
    ⟨m32_272.1, m32_272.2.1, fun i hi => (bytes33 272 32 (by decide) (by decide) (by decide) i hi).trans (m32_272.2.2 i hi)⟩
  have m33_496 : MontgomeryAt t33 (stackPtr s - BitVec.ofNat 64 496) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p (values point).xProduct ((values point).bxz6 * (values point).yz2 % P256.Spec.Operations.domain.p)) :=
    ⟨m32_496.1, m32_496.2.1, fun i hi => (bytes33 496 32 (by decide) (by decide) (by decide) i hi).trans (m32_496.2.2 i hi)⟩
  have m33_688 : MontgomeryAt t33 (stackPtr s - BitVec.ofNat 64 688) ((((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p) + ((values point).yz2 * (values point).yy % P256.Spec.Operations.domain.p)) % P256.Spec.Operations.domain.p) :=
    ⟨m32_688.1, m32_688.2.1, fun i hi => (bytes33 688 32 (by decide) (by decide) (by decide) i hi).trans (m32_688.2.2 i hi)⟩
  exact ⟨_, t33, (((((((((((((((run18.trans run19).trans run20).trans run21).trans run22).trans run23).trans run24).trans run25).trans run26).trans run27).trans run28).trans run29).trans run30).trans run31).trans run32).trans run33), frame33, rip33,
    r33_rbx, m33_496, m33_272, value33⟩

end P256.Proofs.Projective.Double
