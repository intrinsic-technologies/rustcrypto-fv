import X86Proofs.Instructions.Nop.Triple
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Steps

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def roundPrepareComponents (base : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 14, .reg 8, .reg 9, .reg 5, .reg 15, .reg 13, .flags, .rip,
    .mem (base + 0x10) 8, .mem (base + 0x18) 8, .mem (base + 0x20) 8, .mem (base + 0x28) 8]

theorem prepare_round [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (frame : ExponentFrame s t) (hip : t.RIP = 0x115514) :
    ∃ u, Advances boundary 16 t u ∧ ExponentFrame s u ∧ u.RIP = 0x115550 ∧
      (∀ r ∈ ([1,14,8,9,5,15,13] : List (BitVec 5)), (Operand.reg r : Operand 64).read u = 0) ∧
      ((Operand.mem (exponentFrameBase s + 0x10) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x68) : Operand 64).read t) ∧
      ((Operand.mem (exponentFrameBase s + 0x18) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x60) : Operand 64).read t) ∧
      ((Operand.mem (exponentFrameBase s + 0x20) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x58) : Operand 64).read t) ∧
      ((Operand.mem (exponentFrameBase s + 0x28) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x50) : Operand 64).read t) ∧
      AgreesExcept (roundPrepareComponents (exponentFrameBase s)) t u := by
  obtain ⟨t1, e1, f1, i1, w1, a1⟩ := load_stack ctx frame
    0x15514 0x48 0 (.sib 4 none 0 (.d8 104)) 0x68
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide)
      (by decide) (by decide +kernel) hip
  change AgreesExcept [.reg 0, .rip] t t1 at a1
  obtain ⟨t2, e2, f2, i2, w2, a2⟩ := store_stack ctx f1
    0x15519 0x48 0 (.sib 4 none 0 (.d8 16)) 0x10
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i1
  obtain ⟨t3, e3, f3, i3, w3, a3⟩ := load_stack ctx f2
    0x1551e 0x48 0 (.sib 4 none 0 (.d8 96)) 0x60
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide)
      (by decide) (by decide +kernel) i2
  change AgreesExcept [.reg 0, .rip] t2 t3 at a3
  obtain ⟨t4, e4, f4, i4, w4, a4⟩ := store_stack ctx f3
    0x15523 0x48 0 (.sib 4 none 0 (.d8 24)) 0x18
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i3
  obtain ⟨t5, e5, f5, i5, w5, a5⟩ := load_stack ctx f4
    0x15528 0x48 0 (.sib 4 none 0 (.d8 88)) 0x58
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide)
      (by decide) (by decide +kernel) i4
  change AgreesExcept [.reg 0, .rip] t4 t5 at a5
  obtain ⟨t6, e6, f6, i6, w6, a6⟩ := store_stack ctx f5
    0x1552d 0x48 0 (.sib 4 none 0 (.d8 32)) 0x20
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i5
  obtain ⟨t7, e7, f7, i7, w7, a7⟩ := load_stack ctx f6
    0x15532 0x48 0 (.sib 4 none 0 (.d8 80)) 0x50
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide)
      (by decide) (by decide +kernel) i6
  change AgreesExcept [.reg 0, .rip] t6 t7 at a7
  obtain ⟨t8, e8, f8, i8, w8, a8⟩ := store_stack ctx f7
    0x15537 0x48 0 (.sib 4 none 0 (.d8 40)) 0x28
      (by simp [RexWPrefix]) (by constructor <;> decide) rfl rfl (fun _ => rfl)
      (by decide) (by decide) (by unfold scratchOffset; omega)
      (by decide) (by decide +kernel) i7
  obtain ⟨t9, e9, hr9, he9⟩ := (xor_r32_r32_rex_effect_step 0x11553c 0x45 0xc9 (by simp [RexNoWPrefix]) rfl).advances
    (readyToStep f8.machine f8.bindingsSupported)
    (programText_slice (programLoaded_codeIn f8.loaded) 0x1553c [0x45,0x31,0xc9]
      (by decide) (by decide +kernel)) i8
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1553f (by decide)))
  have a9 : AgreesExcept [.reg 9, .flags, .rip] t8 t9 := he9.agrees
  have f9 := f8.of_registers hr9 a9 (by simp) (by simp [Component.Covers])
  have i9 : t9.RIP = 0x11553f := he9.rip
  have w9 : (Operand.reg 9 : Operand 64).read t9 = 0 := by
    have hw := he9.writes
    change (Operand.reg 9 : Operand 64).read t9 =
      (((Operand.reg 9 : Operand 32).read t8) ^^^ ((Operand.reg 9 : Operand 32).read t8)).setWidth 64 at hw
    simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using hw
  obtain ⟨t10, e10, hr10, he10⟩ := (xor_r32_r32_rex_effect_step 0x11553f 0x45 0xc0 (by simp [RexNoWPrefix]) rfl).advances
    (readyToStep f9.machine f9.bindingsSupported)
    (programText_slice (programLoaded_codeIn f9.loaded) 0x1553f [0x45,0x31,0xc0]
      (by decide) (by decide +kernel)) i9
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15542 (by decide)))
  have a10 : AgreesExcept [.reg 8, .flags, .rip] t9 t10 := he10.agrees
  have f10 := f9.of_registers hr10 a10 (by simp) (by simp [Component.Covers])
  have i10 : t10.RIP = 0x115542 := he10.rip
  have w10 : (Operand.reg 8 : Operand 64).read t10 = 0 := by
    have hw := he10.writes
    change (Operand.reg 8 : Operand 64).read t10 =
      (((Operand.reg 8 : Operand 32).read t9) ^^^ ((Operand.reg 8 : Operand 32).read t9)).setWidth 64 at hw
    simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using hw
  obtain ⟨t11, e11, hr11, he11⟩ := (xor_r32_r32_effect_step 0x115542 0xed rfl).advances
    (readyToStep f10.machine f10.bindingsSupported)
    (programText_slice (programLoaded_codeIn f10.loaded) 0x15542 [0x31,0xed]
      (by decide) (by decide +kernel)) i10
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15544 (by decide)))
  have a11 : AgreesExcept [.reg 5, .flags, .rip] t10 t11 := he11.agrees
  have f11 := f10.of_registers hr11 a11 (by simp) (by simp [Component.Covers])
  have i11 : t11.RIP = 0x115544 := he11.rip
  have w11 : (Operand.reg 5 : Operand 64).read t11 = 0 := by
    have hw := he11.writes
    change (Operand.reg 5 : Operand 64).read t11 =
      (((Operand.reg 5 : Operand 32).read t10) ^^^ ((Operand.reg 5 : Operand 32).read t10)).setWidth 64 at hw
    simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using hw
  obtain ⟨t12, e12, hr12, he12⟩ := (xor_r32_r32_effect_step 0x115544 0xc9 rfl).advances
    (readyToStep f11.machine f11.bindingsSupported)
    (programText_slice (programLoaded_codeIn f11.loaded) 0x15544 [0x31,0xc9]
      (by decide) (by decide +kernel)) i11
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15546 (by decide)))
  have a12 : AgreesExcept [.reg 1, .flags, .rip] t11 t12 := he12.agrees
  have f12 := f11.of_registers hr12 a12 (by simp) (by simp [Component.Covers])
  have i12 : t12.RIP = 0x115546 := he12.rip
  have w12 : (Operand.reg 1 : Operand 64).read t12 = 0 := by
    have hw := he12.writes
    change (Operand.reg 1 : Operand 64).read t12 =
      (((Operand.reg 1 : Operand 32).read t11) ^^^ ((Operand.reg 1 : Operand 32).read t11)).setWidth 64 at hw
    simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using hw
  obtain ⟨t13, e13, hr13, he13⟩ := (xor_r32_r32_rex_effect_step 0x115546 0x45 0xed (by simp [RexNoWPrefix]) rfl).advances
    (readyToStep f12.machine f12.bindingsSupported)
    (programText_slice (programLoaded_codeIn f12.loaded) 0x15546 [0x45,0x31,0xed]
      (by decide) (by decide +kernel)) i12
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15549 (by decide)))
  have a13 : AgreesExcept [.reg 13, .flags, .rip] t12 t13 := he13.agrees
  have f13 := f12.of_registers hr13 a13 (by simp) (by simp [Component.Covers])
  have i13 : t13.RIP = 0x115549 := he13.rip
  have w13 : (Operand.reg 13 : Operand 64).read t13 = 0 := by
    have hw := he13.writes
    change (Operand.reg 13 : Operand 64).read t13 =
      (((Operand.reg 13 : Operand 32).read t12) ^^^ ((Operand.reg 13 : Operand 32).read t12)).setWidth 64 at hw
    simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using hw
  obtain ⟨t14, e14, hr14, he14⟩ := (xor_r32_r32_rex_effect_step 0x115549 0x45 0xff (by simp [RexNoWPrefix]) rfl).advances
    (readyToStep f13.machine f13.bindingsSupported)
    (programText_slice (programLoaded_codeIn f13.loaded) 0x15549 [0x45,0x31,0xff]
      (by decide) (by decide +kernel)) i13
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1554c (by decide)))
  have a14 : AgreesExcept [.reg 15, .flags, .rip] t13 t14 := he14.agrees
  have f14 := f13.of_registers hr14 a14 (by simp) (by simp [Component.Covers])
  have i14 : t14.RIP = 0x11554c := he14.rip
  have w14 : (Operand.reg 15 : Operand 64).read t14 = 0 := by
    have hw := he14.writes
    change (Operand.reg 15 : Operand 64).read t14 =
      (((Operand.reg 15 : Operand 32).read t13) ^^^ ((Operand.reg 15 : Operand 32).read t13)).setWidth 64 at hw
    simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using hw
  obtain ⟨t15, e15, hr15, he15⟩ := (xor_r32_r32_rex_effect_step 0x11554c 0x45 0xf6 (by simp [RexNoWPrefix]) rfl).advances
    (readyToStep f14.machine f14.bindingsSupported)
    (programText_slice (programLoaded_codeIn f14.loaded) 0x1554c [0x45,0x31,0xf6]
      (by decide) (by decide +kernel)) i14
    (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1554f (by decide)))
  have a15 : AgreesExcept [.reg 14, .flags, .rip] t14 t15 := he15.agrees
  have f15 := f14.of_registers hr15 a15 (by simp) (by simp [Component.Covers])
  have i15 : t15.RIP = 0x11554f := he15.rip
  have w15 : (Operand.reg 14 : Operand 64).read t15 = 0 := by
    have hw := he15.writes
    change (Operand.reg 14 : Operand 64).read t15 =
      (((Operand.reg 14 : Operand 32).read t14) ^^^ ((Operand.reg 14 : Operand 32).read t14)).setWidth 64 at hw
    simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using hw
  obtain ⟨u, e16, hr16, he16⟩ :=
    (nop_effect_step 0x11554f).advances (readyToStep f15.machine f15.bindingsSupported)
      (programText_slice (programLoaded_codeIn f15.loaded) 0x1554f
        [0x90] (by decide) (by decide +kernel)) i15
      (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15550 (by decide)))
  have a16 : AgreesExcept [.rip] t15 u := he16.agrees
  have f16 := f15.of_registers hr16 a16 (by simp) (by simp [Component.Covers])
  have memoryTail : ∀ address : BitVec 64, u.external[address]? = t8.external[address]? :=
    fun address => congrArg (fun m : Ram => m[address]?)
      ((((((((a9.trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans a16).external (by simp [Component.Covers]))
  refine ⟨u, (((((((((((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7).trans e8).trans e9).trans e10).trans e11).trans e12).trans e13).trans e14).trans e15).trans e16), f16, he16.rip, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (a16.read (n := 64) (r := 1) (by simp)).trans ((a15.read (n := 64) (r := 1) (by simp)).trans ((a14.read (n := 64) (r := 1) (by simp)).trans ((a13.read (n := 64) (r := 1) (by simp)).trans (w12))))
    · exact (a16.read (n := 64) (r := 14) (by simp)).trans (w15)
    · exact (a16.read (n := 64) (r := 8) (by simp)).trans ((a15.read (n := 64) (r := 8) (by simp)).trans ((a14.read (n := 64) (r := 8) (by simp)).trans ((a13.read (n := 64) (r := 8) (by simp)).trans ((a12.read (n := 64) (r := 8) (by simp)).trans ((a11.read (n := 64) (r := 8) (by simp)).trans (w10))))))
    · exact (a16.read (n := 64) (r := 9) (by simp)).trans ((a15.read (n := 64) (r := 9) (by simp)).trans ((a14.read (n := 64) (r := 9) (by simp)).trans ((a13.read (n := 64) (r := 9) (by simp)).trans ((a12.read (n := 64) (r := 9) (by simp)).trans ((a11.read (n := 64) (r := 9) (by simp)).trans ((a10.read (n := 64) (r := 9) (by simp)).trans (w9)))))))
    · exact (a16.read (n := 64) (r := 5) (by simp)).trans ((a15.read (n := 64) (r := 5) (by simp)).trans ((a14.read (n := 64) (r := 5) (by simp)).trans ((a13.read (n := 64) (r := 5) (by simp)).trans ((a12.read (n := 64) (r := 5) (by simp)).trans (w11)))))
    · exact (a16.read (n := 64) (r := 15) (by simp)).trans ((a15.read (n := 64) (r := 15) (by simp)).trans (w14))
    · exact (a16.read (n := 64) (r := 13) (by simp)).trans ((a15.read (n := 64) (r := 13) (by simp)).trans ((a14.read (n := 64) (r := 13) (by simp)).trans (w13)))
  · apply Eq.trans (by
      apply memLoad_congr
      intro i hi
      change (u.external[_]?).getD 0 = (t8.external[_]?).getD 0
      rw [memoryTail])
    change (Operand.mem (exponentFrameBase s + 0x10) : Operand 64).read t8 =
      (Operand.mem (exponentFrameBase s + 0x68) : Operand 64).read t
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_store_apart a8 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a7,
      word_of_store_apart a6 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a5,
      word_of_store_apart a4 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a3,
      w2,
      w1]
  · apply Eq.trans (by
      apply memLoad_congr
      intro i hi
      change (u.external[_]?).getD 0 = (t8.external[_]?).getD 0
      rw [memoryTail])
    change (Operand.mem (exponentFrameBase s + 0x18) : Operand 64).read t8 =
      (Operand.mem (exponentFrameBase s + 0x60) : Operand 64).read t
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_store_apart a8 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a7,
      word_of_store_apart a6 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a5,
      w4,
      w3]
    rw [word_of_store_apart a2 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a1]
  · apply Eq.trans (by
      apply memLoad_congr
      intro i hi
      change (u.external[_]?).getD 0 = (t8.external[_]?).getD 0
      rw [memoryTail])
    change (Operand.mem (exponentFrameBase s + 0x20) : Operand 64).read t8 =
      (Operand.mem (exponentFrameBase s + 0x58) : Operand 64).read t
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word_of_store_apart a8 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a7,
      w6,
      w5]
    rw [word_of_store_apart a4 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a3,
      word_of_store_apart a2 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a1]
  · apply Eq.trans (by
      apply memLoad_congr
      intro i hi
      change (u.external[_]?).getD 0 = (t8.external[_]?).getD 0
      rw [memoryTail])
    change (Operand.mem (exponentFrameBase s + 0x28) : Operand 64).read t8 =
      (Operand.mem (exponentFrameBase s + 0x50) : Operand 64).read t
    simp only [BitVec.ofNat_eq_ofNat]
    rw [w8,
      w7]
    rw [word_of_store_apart a6 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a5,
      word_of_store_apart a4 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a3,
      word_of_store_apart a2 (by unfold OffsetsApart; decide +kernel),
      word_of_registers a1]
  · exact (((((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans a16).mono (by
      intro c hm
      simp only [roundPrepareComponents, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      grind only)

end P256.Proofs.Sec1.SquareRoot.SquareFour
