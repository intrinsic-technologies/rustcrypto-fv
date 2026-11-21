import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Steps

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hf : ExponentFrame s t)
    (hc : ExponentConstants s t x) (hip : t.RIP = 0x11581c) :
    ∃ u, Advances boundary 13 t u ∧ ExponentFrame s u ∧ ExponentConstants s u x ∧
      u.RIP = 0x11586c ∧ u.regValue .r15 = s.regValue .rsi + 32 ∧ u.regValue .rbx = 3 ∧
      u.regValue .r13 = 15 ∧ u.regValue .r11 = t.regValue .r11 ∧ u.regValue .r12 = t.regValue .r12 ∧
      u.regValue .rbp = (Operand.mem (exponentFrameBase s + 0x2c0) : Operand 64).read t ∧
      u.regValue .r14 = (Operand.mem (exponentFrameBase s + 0x2d0) : Operand 64).read t ∧
      ((Operand.mem (exponentFrameBase s + 0x30) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x68) : Operand 64).read t) ∧
      ((Operand.mem (exponentFrameBase s + 0x38) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x60) : Operand 64).read t) ∧
      ((Operand.mem (exponentFrameBase s + 0x40) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x58) : Operand 64).read t) ∧
      ((Operand.mem (exponentFrameBase s + 0x48) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x50) : Operand 64).read t) ∧
      AgreesExcept (components (exponentFrameBase s)) t u := by
  obtain ⟨t1, e1, f1, i1, w1, a1⟩ :=
    load_stack h hf 0x1581c 0x48 0 (.sib 4 none 0 (.d8 0x68)) 0x68
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) hip
  obtain ⟨t2, e2, f2, i2, w2, a2⟩ :=
    store_stack h f1 0x15821 0x48 0 (.sib 4 none 0 (.d8 0x30)) 0x30
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i1
  obtain ⟨t3, e3, f3, i3, w3, a3⟩ :=
    load_stack h f2 0x15826 0x48 0 (.sib 4 none 0 (.d8 0x60)) 0x60
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i2
  obtain ⟨t4, e4, f4, i4, w4, a4⟩ :=
    store_stack h f3 0x1582b 0x48 0 (.sib 4 none 0 (.d8 0x38)) 0x38
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i3
  obtain ⟨t5, e5, f5, i5, w5, a5⟩ :=
    load_stack h f4 0x15830 0x48 0 (.sib 4 none 0 (.d8 0x58)) 0x58
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i4
  obtain ⟨t6, e6, f6, i6, w6, a6⟩ :=
    store_stack h f5 0x15835 0x48 0 (.sib 4 none 0 (.d8 0x40)) 0x40
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i5
  obtain ⟨t7, e7, f7, i7, w7, a7⟩ :=
    load_stack h f6 0x1583a 0x48 0 (.sib 4 none 0 (.d8 0x50)) 0x50
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i6
  obtain ⟨t8, e8, f8, i8, w8, a8⟩ :=
    store_stack h f7 0x1583f 0x48 0 (.sib 4 none 0 (.d8 0x48)) 0x48
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i7
  obtain ⟨t9, e9, f9, i9, w9, a9⟩ :=
    load_stack h f8 0x15844 0x4c 7 (.sib 4 none 0 (.d32 0x2b8)) 0x2b8
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i8
  obtain ⟨t10, e10, f10, i10, w10, a10⟩ :=
    load_stack h f9 0x1584c 0x48 3 (.sib 4 none 0 (.d32 0x2b0)) 0x2b0
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i9
  obtain ⟨t11, e11, f11, i11, w11, a11⟩ :=
    load_stack h f10 0x15854 0x4c 5 (.sib 4 none 0 (.d32 0x2a8)) 0x2a8
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i10
  obtain ⟨t12, e12, f12, i12, w12, a12⟩ :=
    load_stack h f11 0x1585c 0x48 5 (.sib 4 none 0 (.d32 0x2c0)) 0x2c0
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i11
  obtain ⟨t13, e13, f13, i13, w13, a13⟩ :=
    load_stack h f12 0x15864 0x4c 6 (.sib 4 none 0 (.d32 0x2d0)) 0x2d0
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i12
  have b1 : AgreesExcept (components (exponentFrameBase s)) t t1 := a1.mono (by simp [components, gprNumber, rexR])
  have b2 := store_agrees a2 (by unfold scratchOffset; omega)
  have b3 : AgreesExcept (components (exponentFrameBase s)) t2 t3 := a3.mono (by simp [components, gprNumber, rexR])
  have b4 := store_agrees a4 (by unfold scratchOffset; omega)
  have b5 : AgreesExcept (components (exponentFrameBase s)) t4 t5 := a5.mono (by simp [components, gprNumber, rexR])
  have b6 := store_agrees a6 (by unfold scratchOffset; omega)
  have b7 : AgreesExcept (components (exponentFrameBase s)) t6 t7 := a7.mono (by simp [components, gprNumber, rexR])
  have b8 := store_agrees a8 (by unfold scratchOffset; omega)
  have b9 : AgreesExcept (components (exponentFrameBase s)) t8 t9 := a9.mono (by simp [components, gprNumber, rexR])
  have b10 : AgreesExcept (components (exponentFrameBase s)) t9 t10 := a10.mono (by simp [components, gprNumber, rexR])
  have b11 : AgreesExcept (components (exponentFrameBase s)) t10 t11 := a11.mono (by simp [components, gprNumber, rexR])
  have b12 : AgreesExcept (components (exponentFrameBase s)) t11 t12 := a12.mono (by simp [components, gprNumber, rexR])
  have b13 : AgreesExcept (components (exponentFrameBase s)) t12 t13 := a13.mono (by simp [components, gprNumber, rexR])
  have all : AgreesExcept (components (exponentFrameBase s)) t t13 :=
    ((((((((((((b1.trans b2).trans b3).trans b4).trans b5).trans b6).trans b7).trans b8).trans b9).trans b10).trans b11).trans b12).trans b13).mono (by simp)
  refine ⟨t13, ((((((((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7).trans e8).trans e9).trans e10).trans e11).trans e12).trans e13), f13, constants_of_agrees h hc all, i13,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, all⟩
  · have hw : (Operand.reg 15 : Operand 64).read t9 =
        (Operand.mem (exponentFrameBase s + BitVec.ofNat 64 696) : Operand 64).read t8 := w9
    have hs : AgreesExcept (components (exponentFrameBase s)) t t8 :=
      (((((((b1.trans b2).trans b3).trans b4).trans b5).trans b6).trans b7).trans b8).mono (by simp)
    exact ((((a10.trans a11).trans a12).trans a13).read (n := 64) (r := 15) (by simp [gprNumber, rexR])).trans
      (hw.trans ((word_of_agrees hs 696 (by decide) (by unfold scratchOffset; omega)).trans hc.parameterPointer))
  · have hw : (Operand.reg 3 : Operand 64).read t10 =
        (Operand.mem (exponentFrameBase s + BitVec.ofNat 64 688) : Operand 64).read t9 := w10
    have hs : AgreesExcept (components (exponentFrameBase s)) t t9 :=
      ((((((((b1.trans b2).trans b3).trans b4).trans b5).trans b6).trans b7).trans b8).trans b9).mono (by simp)
    exact (((a11.trans a12).trans a13).read (n := 64) (r := 3) (by simp [gprNumber, rexR])).trans
      (hw.trans ((word_of_agrees hs 688 (by decide) (by unfold scratchOffset; omega)).trans hc.firstWord))
  · have hw : (Operand.reg 13 : Operand 64).read t11 =
        (Operand.mem (exponentFrameBase s + BitVec.ofNat 64 680) : Operand 64).read t10 := w11
    have hs : AgreesExcept (components (exponentFrameBase s)) t t10 :=
      (((((((((b1.trans b2).trans b3).trans b4).trans b5).trans b6).trans b7).trans b8).trans b9).trans b10).mono (by simp)
    exact ((a12.trans a13).read (n := 64) (r := 13) (by simp [gprNumber, rexR])).trans
      (hw.trans ((word_of_agrees hs 680 (by decide) (by unfold scratchOffset; omega)).trans hc.firstWindow))
  · exact ((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).read (n := 64) (r := 11) (by simp [gprNumber, rexR])
  · exact ((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).read (n := 64) (r := 12) (by simp [gprNumber, rexR])
  · change (Operand.reg 5 : Operand 64).read t13 = _
    simp only [BitVec.ofNat_eq_ofNat]
    rw [a13.read (n := 64) (r := 5#5) (by simp [gprNumber, rexR])]
    change (Operand.reg 5#5 : Operand 64).read t12 =
      (Operand.mem (exponentFrameBase s + 704#64) : Operand 64).read t11 at w12
    rw [w12, word_of_registers a11,
      word_of_registers a10,
      word_of_registers a9,
      word_of_store_apart a8 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a7,
      word_of_store_apart a6 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a5,
      word_of_store_apart a4 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a3,
      word_of_store_apart a2 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a1]
  · change (Operand.reg 14 : Operand 64).read t13 = _
    simp only [BitVec.ofNat_eq_ofNat]
    change (Operand.reg 14#5 : Operand 64).read t13 =
      (Operand.mem (exponentFrameBase s + 720#64) : Operand 64).read t12 at w13
    rw [w13, word_of_registers a12,
      word_of_registers a11,
      word_of_registers a10,
      word_of_registers a9,
      word_of_store_apart a8 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a7,
      word_of_store_apart a6 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a5,
      word_of_store_apart a4 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a3,
      word_of_store_apart a2 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a1]
  · change (Operand.mem _ : Operand 64).read t13 = _
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_registers a13,
      word_of_registers a12,
      word_of_registers a11,
      word_of_registers a10,
      word_of_registers a9,
      word_of_store_apart a8 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a7,
      word_of_store_apart a6 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a5,
      word_of_store_apart a4 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a3, w2, w1]
  · change (Operand.mem _ : Operand 64).read t13 = _
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_registers a13,
      word_of_registers a12,
      word_of_registers a11,
      word_of_registers a10,
      word_of_registers a9,
      word_of_store_apart a8 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a7,
      word_of_store_apart a6 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a5, w4, w3]
    rw [word_of_store_apart a2 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a1]
  · change (Operand.mem _ : Operand 64).read t13 = _
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_registers a13,
      word_of_registers a12,
      word_of_registers a11,
      word_of_registers a10,
      word_of_registers a9,
      word_of_store_apart a8 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a7, w6, w5]
    rw [word_of_store_apart a4 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a3,
      word_of_store_apart a2 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a1]
  · change (Operand.mem _ : Operand 64).read t13 = _
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_registers a13,
      word_of_registers a12,
      word_of_registers a11,
      word_of_registers a10,
      word_of_registers a9, w8, w7]
    rw [word_of_store_apart a6 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a5,
      word_of_store_apart a4 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a3,
      word_of_store_apart a2 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a1]

end P256.Proofs.Sec1.SquareRoot.SquareFour
