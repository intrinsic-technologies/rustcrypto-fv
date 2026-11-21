import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Steps

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hf : ExponentFrame s t)
    (hc : ExponentConstants s t x) (hip : t.RIP = 0x1154d6) :
    ∃ u, Advances boundary 11 t u ∧ ExponentFrame s u ∧ ExponentConstants s u x ∧
      u.RIP = 0x115510 ∧ u.regValue .rax = 0 ∧ u.regValue .rbx = 0xffffffff ∧
      u.regValue .r11 = t.regValue .r11 ∧ u.regValue .r12 = t.regValue .r12 ∧
      exponentWordAt u (exponentFrameBase s + 0x2d0) (t.regValue .r14) ∧
      ((Operand.mem (exponentFrameBase s + 0x68) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x30) : Operand 64).read t) ∧
      ((Operand.mem (exponentFrameBase s + 0x60) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x38) : Operand 64).read t) ∧
      ((Operand.mem (exponentFrameBase s + 0x58) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x40) : Operand 64).read t) ∧
      ((Operand.mem (exponentFrameBase s + 0x50) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x48) : Operand 64).read t) ∧
      AgreesExcept (components (exponentFrameBase s)) t u := by
  obtain ⟨t1, e1, f1, i1, w1, a1⟩ :=
    store_stack h hf 0x154d6 0x4c 6 (.sib 4 none 0 (.d32 0x2d0)) 0x2d0
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) hip
  obtain ⟨t2, e2, f2, i2, w2, a2⟩ :=
    load_stack h f1 0x154de 0x48 0 (.sib 4 none 0 (.d8 0x30)) 0x30
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i1
  obtain ⟨t3, e3, f3, i3, w3, a3⟩ :=
    store_stack h f2 0x154e3 0x48 0 (.sib 4 none 0 (.d8 0x68)) 0x68
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i2
  obtain ⟨t4, e4, f4, i4, w4, a4⟩ :=
    load_stack h f3 0x154e8 0x48 0 (.sib 4 none 0 (.d8 0x38)) 0x38
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i3
  obtain ⟨t5, e5, f5, i5, w5, a5⟩ :=
    store_stack h f4 0x154ed 0x48 0 (.sib 4 none 0 (.d8 0x60)) 0x60
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i4
  obtain ⟨t6, e6, f6, i6, w6, a6⟩ :=
    load_stack h f5 0x154f2 0x48 0 (.sib 4 none 0 (.d8 0x40)) 0x40
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i5
  obtain ⟨t7, e7, f7, i7, w7, a7⟩ :=
    store_stack h f6 0x154f7 0x48 0 (.sib 4 none 0 (.d8 0x58)) 0x58
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i6
  obtain ⟨t8, e8, f8, i8, w8, a8⟩ :=
    load_stack h f7 0x154fc 0x48 0 (.sib 4 none 0 (.d8 0x48)) 0x48
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) i7
  obtain ⟨t9, e9, f9, i9, w9, a9⟩ :=
    store_stack h f8 0x15501 0x48 0 (.sib 4 none 0 (.d8 0x50)) 0x50
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i8
  obtain ⟨t10, e10, r10, h10⟩ :=
    (xor_r32_r32_effect_step 0x115506 0xc0 (by decide)).advances
      (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x15506 _ (by decide) (by decide +kernel)) i9
      (boundary_ne_program h.outerBoundary (inProgram_of_textOffset 0x15508 (by decide)))
  have a10 : AgreesExcept [.reg 0, .flags, .rip] t9 t10 := h10.agrees
  have f10 := ExponentFrame.of_registers f9 r10 a10 (by simp) (by simp [Component.Covers])
  have w10 : t10.regValue .rax = 0 := by
    have hw := h10.writes
    change t10.regValue .rax =
      (((Operand.reg 0 : Operand 32).read t9) ^^^ ((Operand.reg 0 : Operand 32).read t9)).setWidth 64 at hw
    simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using hw
  obtain ⟨t11, e11, f11, i11, w11, a11⟩ :=
    load_stack h f10 0x15508 0x48 3 (.sib 4 none 0 (.d32 0x80)) 0x80
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by decide) (by decide +kernel) h10.rip
  have b1 := store_agrees a1 (by unfold scratchOffset; omega)
  have b2 : AgreesExcept (components (exponentFrameBase s)) t1 t2 := a2.mono (by simp [components, gprNumber, rexR])
  have b3 := store_agrees a3 (by unfold scratchOffset; omega)
  have b4 : AgreesExcept (components (exponentFrameBase s)) t3 t4 := a4.mono (by simp [components, gprNumber, rexR])
  have b5 := store_agrees a5 (by unfold scratchOffset; omega)
  have b6 : AgreesExcept (components (exponentFrameBase s)) t5 t6 := a6.mono (by simp [components, gprNumber, rexR])
  have b7 := store_agrees a7 (by unfold scratchOffset; omega)
  have b8 : AgreesExcept (components (exponentFrameBase s)) t7 t8 := a8.mono (by simp [components, gprNumber, rexR])
  have b9 := store_agrees a9 (by unfold scratchOffset; omega)
  have b10 : AgreesExcept (components (exponentFrameBase s)) t9 t10 := a10.mono (by simp [components])
  have b11 : AgreesExcept (components (exponentFrameBase s)) t10 t11 := a11.mono (by simp [components, gprNumber, rexR])
  have all : AgreesExcept (components (exponentFrameBase s)) t t11 :=
    ((((((((((b1.trans b2).trans b3).trans b4).trans b5).trans b6).trans b7).trans b8).trans b9).trans b10).trans b11).mono (by simp)
  refine ⟨t11, ((((((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7).trans e8).trans e9).trans e10).trans e11), f11, constants_of_agrees h hc all, i11,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, all⟩
  · exact (a11.read (n := 64) (r := 0) (by simp [gprNumber, rexR])).trans w10
  · have hw : t11.regValue .rbx = (Operand.mem (exponentFrameBase s + 0x80) : Operand 64).read t10 := w11
    have hs : AgreesExcept (components (exponentFrameBase s)) t t10 :=
      (((((((((b1.trans b2).trans b3).trans b4).trans b5).trans b6).trans b7).trans b8).trans b9).trans b10).mono (by simp)
    exact hw.trans ((word_of_agrees hs 0x80 (by decide) (by unfold scratchOffset; omega)).trans hc.modulus1)
  · exact ((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).read (n := 64) (r := 11) (by simp [gprNumber, rexR])
  · exact ((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).read (n := 64) (r := 12) (by simp [gprNumber, rexR])
  · change (Operand.mem _ : Operand 64).read t11 = _
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_registers a11,
      P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees a10 _ (by simp [Component.Covers]),
      word_of_store_apart a9 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a8,
      word_of_store_apart a7 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a6,
      word_of_store_apart a5 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a4,
      word_of_store_apart a3 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a2, w1]
    rfl
  · change (Operand.mem _ : Operand 64).read t11 = _
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_registers a11,
      P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees a10 _ (by simp [Component.Covers]),
      word_of_store_apart a9 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a8,
      word_of_store_apart a7 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a6,
      word_of_store_apart a5 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a4, w3]
    rw [w2]
    rw [word_of_store_apart a1 (by unfold OffsetsApart; decide +kernel)]
  · change (Operand.mem _ : Operand 64).read t11 = _
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_registers a11,
      P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees a10 _ (by simp [Component.Covers]),
      word_of_store_apart a9 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a8,
      word_of_store_apart a7 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a6, w5]
    rw [w4]
    rw [word_of_store_apart a3 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a2,
      word_of_store_apart a1 (by unfold OffsetsApart; decide +kernel)]
  · change (Operand.mem _ : Operand 64).read t11 = _
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_registers a11,
      P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees a10 _ (by simp [Component.Covers]),
      word_of_store_apart a9 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a8, w7]
    rw [w6]
    rw [word_of_store_apart a5 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a4,
      word_of_store_apart a3 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a2,
      word_of_store_apart a1 (by unfold OffsetsApart; decide +kernel)]
  · change (Operand.mem _ : Operand 64).read t11 = _
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_registers a11,
      P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees a10 _ (by simp [Component.Covers]), w9]
    rw [w8]
    rw [word_of_store_apart a7 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a6,
      word_of_store_apart a5 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a4,
      word_of_store_apart a3 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a2,
      word_of_store_apart a1 (by unfold OffsetsApart; decide +kernel)]

end P256.Proofs.Sec1.SquareRoot.SquareFour
