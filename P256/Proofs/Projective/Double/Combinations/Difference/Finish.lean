import P256.Proofs.Projective.Double.Combinations.Difference.Prepare

set_option autoImplicit false


namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Combinations
open CrossTerms (slot_add store_writes)

set_option maxRecDepth 2048 in
theorem Combinations.difference_finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x106224)
    (input : ZZSumAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x10623a ∧ DifferenceAt s u point := by
  let v21 := (tripleZZ point + (values point).xx) % Operations.domain.p
  have frame21 := state
  have rip21 := rip
  have m21_72 := input.sum
  have r21_r14 := input.r14
  have r21_rbp := input.rbp
  have m21_0_232 := input.bxz
  have point21 := input.pointAt
  have r21_rbx := input.rbx
  have r21_r15 := input.r15
  have r21_r12 := input.r12
  have m21_0_104 := input.xx
  have m21_0_136 := input.yy
  have m21_0_520 := input.xProduct
  have m21_0_616 := input.yProduct
  have m21_0_360 := input.zz3
  obtain ⟨t22, run22, frame22, effect22⟩ := step_registers pre frame21
    (offset := 0x6224) (lea_r64_effect_step 0x106224 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 392)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip21
    (inProgram_of_textOffset 0x622c (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 13, .rip]; decide +kernel)
  have ag22 : AgreesExcept [.reg 13, .rip] t t22 := effect22.agrees
  have ext22 : t22.external = t.external := ag22.external (by simp [Component.Covers])
  have rip22 : t22.RIP = 0x10622c := effect22.rip
  have write22 : t22.regValue .r13 = stackPtr t + 392#64 := effect22.writes
  rw [frame21.rsp] at write22
  have r22_r13 : t22.regValue .r13 = stackSlot s 392 := write22
  obtain ⟨t23, run23, frame23, effect23⟩ := step_registers pre frame22
    (offset := 0x622c) (mov_r64_r64_effect_step 0x10622c 0x4c 0xef (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip22
    (inProgram_of_textOffset 0x622f (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have ag23 : AgreesExcept [.reg 7, .rip] t22 t23 := effect23.agrees
  have ext23 : t23.external = t22.external := ag23.external (by simp [Component.Covers])
  have rip23 : t23.RIP = 0x10622f := effect23.rip
  have write23 : t23.regValue .rdi = t22.regValue .r13 := effect23.writes
  have r23_rdi : t23.regValue .rdi = stackSlot s 392 := write23.trans r22_r13
  have r22_r14 : t22.regValue .r14 = stackSlot s 232 :=
    (ag22.read (n := 64) (r := 14) (by simp)).trans r21_r14
  have r23_r14 : t23.regValue .r14 = stackSlot s 232 :=
    (ag23.read (n := 64) (r := 14) (by simp)).trans r22_r14
  obtain ⟨t24, run24, frame24, effect24⟩ := step_registers pre frame23
    (offset := 0x622f) (mov_r64_r64_effect_step 0x10622f 0x4c 0xf6 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip23
    (inProgram_of_textOffset 0x6232 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have ag24 : AgreesExcept [.reg 6, .rip] t23 t24 := effect24.agrees
  have ext24 : t24.external = t23.external := ag24.external (by simp [Component.Covers])
  have rip24 : t24.RIP = 0x106232 := effect24.rip
  have write24 : t24.regValue .rsi = t23.regValue .r14 := effect24.writes
  have r24_rsi : t24.regValue .rsi = stackSlot s 232 := write24.trans r23_r14
  have r22_rbp : t22.regValue .rbp = stackSlot s 72 :=
    (ag22.read (n := 64) (r := 5) (by simp)).trans r21_rbp
  have r23_rbp : t23.regValue .rbp = stackSlot s 72 :=
    (ag23.read (n := 64) (r := 5) (by simp)).trans r22_rbp
  have r24_rbp : t24.regValue .rbp = stackSlot s 72 :=
    (ag24.read (n := 64) (r := 5) (by simp)).trans r23_rbp
  obtain ⟨t25, run25, frame25, effect25⟩ := step_registers pre frame24
    (offset := 0x6232) (mov_r64_r64_effect_step 0x106232 0x48 0xea (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip24
    (inProgram_of_textOffset 0x6235 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 2, .rip]; decide +kernel)
  have ag25 : AgreesExcept [.reg 2, .rip] t24 t25 := effect25.agrees
  have ext25 : t25.external = t24.external := ag25.external (by simp [Component.Covers])
  have rip25 : t25.RIP = 0x106235 := effect25.rip
  have write25 : t25.regValue .rdx = t24.regValue .rbp := effect25.writes
  have r25_rdx : t25.regValue .rdx = stackSlot s 72 := write25.trans r24_rbp
  have r24_rdi : t24.regValue .rdi = stackSlot s 392 :=
    (ag24.read (n := 64) (r := 7) (by simp)).trans r23_rdi
  have r25_rdi : t25.regValue .rdi = stackSlot s 392 :=
    (ag25.read (n := 64) (r := 7) (by simp)).trans r24_rdi
  have r25_rsi : t25.regValue .rsi = stackSlot s 232 :=
    (ag25.read (n := 64) (r := 6) (by simp)).trans r24_rsi
  have m22_0_232 : MontgomeryAt t22 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_0_232
  have m23_0_232 : MontgomeryAt t23 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_0_232
  have m24_0_232 : MontgomeryAt t24 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext24] using m23_0_232
  have m25_0_232 : MontgomeryAt t25 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_232
  have m22_21_72 : MontgomeryAt t22 (stackSlot s 72) (v21) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_72
  have m23_21_72 : MontgomeryAt t23 (stackSlot s 72) (v21) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_21_72
  have m24_21_72 : MontgomeryAt t24 (stackSlot s 72) (v21) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext24] using m23_21_72
  have m25_21_72 : MontgomeryAt t25 (stackSlot s 72) (v21) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_21_72
  let v26 : Nat := Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p (bXZ point) (v21)
  let site26 : BinaryCallSite 1016 728 0x1137e0 24 :=
    { codeOffset := 0x6235, disp := 0xd5a6, codeBound := by decide,
      bytes := by decide +kernel, target := by decide +kernel, entryLow := by decide,
      entryProgram := inProgram_of_textOffset 0x137e0 (by decide),
      layout := ⟨736, 496, 336, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, stack := rfl, outputSaved := by decide,
      rightOffset := 656, rightAbove := by decide, rightEnd := by decide,
      rightApart := by decide }
  obtain ⟨n26, t26, run26, frame26, rip26, value26, regs26, bytes26, work26⟩ :=
    binary_call pre frame25 (x := bXZ point) (y := v21)
      (op := Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p) site26
      (fun _ hp hx hy => by simpa only [Standards.SECG.ECC.Curve.fieldSub, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] using field_subtract_correct hp hx hy)
      rip25
      (by simpa only [stackSlot_eq s (show 232 ≤ 728 by decide)] using r25_rsi)
      (by simpa only [stackSlot_eq s (show 72 ≤ 728 by decide)] using r25_rdx)
      (by simpa only [stackSlot_eq s (show 392 ≤ 728 by decide)] using r25_rdi)
      (by simpa only [stackSlot_eq s (show 232 ≤ 728 by decide)] using m25_0_232)
      (by simpa only [stackSlot_eq s (show 72 ≤ 728 by decide)] using m25_21_72)
  have m26_392 : MontgomeryAt t26 (stackSlot s 392) v26 := by
    rw [stackSlot_eq s (show 392 ≤ 728 by decide)]
    exact value26
  have point22 : ProjectiveAt t22 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using point21
  have point23 : ProjectiveAt t23 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using point22
  have point24 : ProjectiveAt t24 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext24] using point23
  have point25 : ProjectiveAt t25 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using point24
  have point26 : ProjectiveAt t26 (s.regValue .rdi) point :=
    point_of_stack pre (work_stack_frame pre work26) point25
  have r22_rbx : t22.regValue .rbx = s.regValue .rdi :=
    (ag22.read (n := 64) (r := 3) (by simp)).trans r21_rbx
  have r23_rbx : t23.regValue .rbx = s.regValue .rdi :=
    (ag23.read (n := 64) (r := 3) (by simp)).trans r22_rbx
  have r24_rbx : t24.regValue .rbx = s.regValue .rdi :=
    (ag24.read (n := 64) (r := 3) (by simp)).trans r23_rbx
  have r25_rbx : t25.regValue .rbx = s.regValue .rdi :=
    (ag25.read (n := 64) (r := 3) (by simp)).trans r24_rbx
  have r26_rbx : t26.regValue .rbx = s.regValue .rdi :=
    (regs26 .rbx (by decide)).trans r25_rbx
  have r22_r15 : t22.regValue .r15 = stackSlot s 616 :=
    (ag22.read (n := 64) (r := 15) (by simp)).trans r21_r15
  have r23_r15 : t23.regValue .r15 = stackSlot s 616 :=
    (ag23.read (n := 64) (r := 15) (by simp)).trans r22_r15
  have r24_r15 : t24.regValue .r15 = stackSlot s 616 :=
    (ag24.read (n := 64) (r := 15) (by simp)).trans r23_r15
  have r25_r15 : t25.regValue .r15 = stackSlot s 616 :=
    (ag25.read (n := 64) (r := 15) (by simp)).trans r24_r15
  have r26_r15 : t26.regValue .r15 = stackSlot s 616 :=
    (regs26 .r15 (by decide)).trans r25_r15
  have r22_r12 : t22.regValue .r12 = stackSlot s 360 :=
    (ag22.read (n := 64) (r := 12) (by simp)).trans r21_r12
  have r23_r12 : t23.regValue .r12 = stackSlot s 360 :=
    (ag23.read (n := 64) (r := 12) (by simp)).trans r22_r12
  have r24_r12 : t24.regValue .r12 = stackSlot s 360 :=
    (ag24.read (n := 64) (r := 12) (by simp)).trans r23_r12
  have r25_r12 : t25.regValue .r12 = stackSlot s 360 :=
    (ag25.read (n := 64) (r := 12) (by simp)).trans r24_r12
  have r26_r12 : t26.regValue .r12 = stackSlot s 360 :=
    (regs26 .r12 (by decide)).trans r25_r12
  have m22_0_104 : MontgomeryAt t22 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_0_104
  have m23_0_104 : MontgomeryAt t23 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_0_104
  have m24_0_104 : MontgomeryAt t24 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext24] using m23_0_104
  have m25_0_104 : MontgomeryAt t25 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_104
  have m26_0_104 : MontgomeryAt t26 (stackSlot s 104) ((values point).xx) :=
    by
    refine ⟨m25_0_104.1, m25_0_104.2.1, fun j hj => ?_⟩
    have h := (bytes26 624 32 (by decide) (by decide) (by decide) j hj)
    have hx := m25_0_104.2.2 j hj
    rw [stackSlot_eq s (show 104 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m22_0_136 : MontgomeryAt t22 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_0_136
  have m23_0_136 : MontgomeryAt t23 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_0_136
  have m24_0_136 : MontgomeryAt t24 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext24] using m23_0_136
  have m25_0_136 : MontgomeryAt t25 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_136
  have m26_0_136 : MontgomeryAt t26 (stackSlot s 136) ((values point).yy) :=
    by
    refine ⟨m25_0_136.1, m25_0_136.2.1, fun j hj => ?_⟩
    have h := (bytes26 592 32 (by decide) (by decide) (by decide) j hj)
    have hx := m25_0_136.2.2 j hj
    rw [stackSlot_eq s (show 136 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m22_0_520 : MontgomeryAt t22 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_0_520
  have m23_0_520 : MontgomeryAt t23 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_0_520
  have m24_0_520 : MontgomeryAt t24 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext24] using m23_0_520
  have m25_0_520 : MontgomeryAt t25 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_520
  have m26_0_520 : MontgomeryAt t26 (stackSlot s 520) ((values point).xProduct) :=
    by
    refine ⟨m25_0_520.1, m25_0_520.2.1, fun j hj => ?_⟩
    have h := (bytes26 208 32 (by decide) (by decide) (by decide) j hj)
    have hx := m25_0_520.2.2 j hj
    rw [stackSlot_eq s (show 520 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m22_0_616 : MontgomeryAt t22 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_0_616
  have m23_0_616 : MontgomeryAt t23 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_0_616
  have m24_0_616 : MontgomeryAt t24 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext24] using m23_0_616
  have m25_0_616 : MontgomeryAt t25 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_616
  have m26_0_616 : MontgomeryAt t26 (stackSlot s 616) ((values point).yProduct) :=
    by
    refine ⟨m25_0_616.1, m25_0_616.2.1, fun j hj => ?_⟩
    have h := (bytes26 112 32 (by decide) (by decide) (by decide) j hj)
    have hx := m25_0_616.2.2 j hj
    rw [stackSlot_eq s (show 616 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m22_0_360 : MontgomeryAt t22 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_0_360
  have m23_0_360 : MontgomeryAt t23 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_0_360
  have m24_0_360 : MontgomeryAt t24 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext24] using m23_0_360
  have m25_0_360 : MontgomeryAt t25 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_360
  have m26_0_360 : MontgomeryAt t26 (stackSlot s 360) (tripleZZ point) :=
    by
    refine ⟨m25_0_360.1, m25_0_360.2.1, fun j hj => ?_⟩
    have h := (bytes26 368 32 (by decide) (by decide) (by decide) j hj)
    have hx := m25_0_360.2.2 j hj
    rw [stackSlot_eq s (show 360 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have r23_r13 : t23.regValue .r13 = stackSlot s 392 :=
    (ag23.read (n := 64) (r := 13) (by simp)).trans r22_r13
  have r24_r13 : t24.regValue .r13 = stackSlot s 392 :=
    (ag24.read (n := 64) (r := 13) (by simp)).trans r23_r13
  have r25_r13 : t25.regValue .r13 = stackSlot s 392 :=
    (ag25.read (n := 64) (r := 13) (by simp)).trans r24_r13
  have r26_r13 : t26.regValue .r13 = stackSlot s 392 :=
    (regs26 .r13 (by decide)).trans r25_r13
  refine ⟨_, t26, ((((run22.trans run23).trans run24).trans run25).trans run26), frame26, rip26, ?_⟩
  exact ⟨⟨point26, r26_rbx, r26_r15, m26_0_104, m26_0_136, m26_0_520, m26_0_616, r26_r12, m26_0_360⟩, r26_r13, m26_392⟩

end P256.Proofs.Projective.Double
