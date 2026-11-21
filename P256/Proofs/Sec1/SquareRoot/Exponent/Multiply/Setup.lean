import P256.Proofs.Sec1.SquareRoot.Exponent.Multiply.State
import P256.Proofs.Common.Field.SquareRoot.Exponent.Multiply.Shift
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

open P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)
open P256.Proofs.Common.Field.SquareRoot.ExponentMultiply (shl_r32_imm8_effect_step shlR32Effect)

namespace P256.Proofs.Sec1.SquareRoot.ExponentMultiply

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n d y : Nat}
    (ctx : ExponentPre s boundary x) (h : ExponentPosition s t x n)
    (hip : t.RIP = 0x1158a2) (hd : d < 16)
    (hdigit : (Operand.reg 0 : Operand 64).read t = BitVec.ofNat 64 d)
    (hacc : MontgomeryAt t (exponentFrameBase s + 0x30) y) :
    ∃ u, Advances boundary 7 t u ∧ CallState s u x n d y := by
  have hp0 := h
  have hr0 := readyToStep h.frame.machine h.frame.bindingsSupported
  have hag0 : AgreesExcept volatileComponents t t := AgreesExcept.refl _ _
  have hn (off : Nat) (ho : off < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 off ≠ boundary.rip :=
    boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset off ho)
  obtain ⟨t1, ha1, hr1, he1⟩ := (shl_r32_imm8_effect_step 0x1158a2 0xe0 5 rfl rfl).advances
    hr0 (programText_slice (programLoaded_codeIn hp0.frame.loaded) 0x158a2 [0xc1, 0xe0, 5]
      (by decide +kernel) rfl) hip (hn 0x158a5 (by decide))
  change (shlR32Effect 0x1158a2 3 0 5 t).Holds t t1 at he1
  have hs1 : AgreesExcept volatileComponents t t1 := (show AgreesExcept [.reg 0, .flags, .rip] t t1 from he1.agrees).mono (by simp [volatileComponents])
  have hp1 := position_of_registers hp0 hr1 hs1
  have hag1 : AgreesExcept volatileComponents t t1 := hs1
  have hv1 : (Operand.reg 0 : Operand 64).read t1 = BitVec.ofNat 64 (32*d) := by
    have hw : (Operand.reg 0 : Operand 64).read t1 =
        ((Operand.reg 0 : Operand 32).read t <<< 5).setWidth 64 := he1.writes
    rw [hw]
    have hd32 : (Operand.reg 0 : Operand 32).read t = BitVec.ofNat 32 d := by
      change ((Operand.reg 0 : Operand 64).read t).setWidth 32 = _
      rw [hdigit, BitVec.setWidth_ofNat_of_le (by decide)]
    rw [hd32]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  let am2 : AddrMode := .sib 4 (some 0) 0 .none
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (lea_r64_effect_step 0x1158a5 0x48 (by simp [RexWPrefix]) 2 am2
      (by constructor <;> decide) rfl rfl).advances hr1
      (programText_slice (programLoaded_codeIn hp1.frame.loaded) 0x158a5
        (0x48 :: 0x8d :: am2.modrm 2 :: am2.tail) (by decide +kernel) (by decide +kernel))
      he1.rip (hn 0x158a9 (by decide))
  change (leaR64Effect 0x1158a5 2 am2 t1).Holds t1 t2 at he2
  have hs2 : AgreesExcept volatileComponents t1 t2 := he2.agrees.mono (by simp [volatileComponents])
  have hp2 := position_of_registers hp1 hr2 hs2
  have hag2 : AgreesExcept volatileComponents t t2 := (hag1.trans hs2).mono (by simp)
  have hv2 : t2.regValue .rdx = exponentFrameBase s + BitVec.ofNat 64 (32*d) := by
    have hw : t2.regValue .rdx = t1.regValue .rsp + ((Operand.reg 0 : Operand 64).read t1 <<< 0) + 0 := he2.writes
    rw [BitVec.shiftLeft_zero] at hw
    change t2.regValue .rdx = t1.regValue .rsp + (Operand.reg 0 : Operand 64).read t1 + (0#64) at hw
    rw [BitVec.add_zero, hp1.frame.rsp, hv1] at hw
    exact hw
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (add_r64_imm32_effect_step 0x1158a9 0x48 0xc2 0x338 (by simp [RexWPrefix]) rfl rfl).advances hr2
      (programText_slice (programLoaded_codeIn hp2.frame.loaded) 0x158a9 [0x48, 0x81, 0xc2, 0x38, 3, 0, 0]
        (by decide +kernel) rfl) he2.rip (hn 0x158b0 (by decide))
  change (addR64Imm32Effect 0x1158a9 2 0x338 t2).Holds t2 t3 at he3
  have hs3 : AgreesExcept volatileComponents t2 t3 := he3.agrees.mono (by simp [volatileComponents])
  have hp3 := position_of_registers hp2 hr3 hs3
  have hag3 : AgreesExcept volatileComponents t t3 := (hag2.trans hs3).mono (by simp)
  have hv3 : t3.regValue .rdx = exponentFrameBase s + 0x338 + BitVec.ofNat 64 (32*d) := by
    have hw : t3.regValue .rdx = t2.regValue .rdx + 0x338 := he3.writes
    rw [hw, hv2]
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (32*d)), ← BitVec.add_assoc]
  let am4 : AddrMode := .sib 4 none 0 (.d8 0x10)
  obtain ⟨t4, ha4, hr4, he4⟩ :=
    (lea_r64_effect_step 0x1158b0 0x48 (by simp [RexWPrefix]) 7 am4
      (by constructor <;> decide) rfl rfl).advances hr3
      (programText_slice (programLoaded_codeIn hp3.frame.loaded) 0x158b0
        (0x48 :: 0x8d :: am4.modrm 7 :: am4.tail) (by decide +kernel) (by decide +kernel))
      he3.rip (hn 0x158b5 (by decide))
  change (leaR64Effect 0x1158b0 7 am4 t3).Holds t3 t4 at he4
  have hs4 : AgreesExcept volatileComponents t3 t4 := he4.agrees.mono (by simp [volatileComponents])
  have hp4 := position_of_registers hp3 hr4 hs4
  have hag4 : AgreesExcept volatileComponents t t4 := (hag3.trans hs4).mono (by simp)
  have hv4 : t4.regValue .rdi = exponentFrameBase s + 0x10 := by
    have hw : t4.regValue .rdi = t3.regValue .rsp + 0x10 := he4.writes
    rw [hw, hp3.frame.rsp]
  let am5 : AddrMode := .sib 4 none 0 (.d8 0x30)
  obtain ⟨t5, ha5, hr5, he5⟩ :=
    (lea_r64_effect_step 0x1158b5 0x48 (by simp [RexWPrefix]) 6 am5
      (by constructor <;> decide) rfl rfl).advances hr4
      (programText_slice (programLoaded_codeIn hp4.frame.loaded) 0x158b5
        (0x48 :: 0x8d :: am5.modrm 6 :: am5.tail) (by decide +kernel) (by decide +kernel))
      he4.rip (hn 0x158ba (by decide))
  change (leaR64Effect 0x1158b5 6 am5 t4).Holds t4 t5 at he5
  have hs5 : AgreesExcept volatileComponents t4 t5 := he5.agrees.mono (by simp [volatileComponents])
  have hp5 := position_of_registers hp4 hr5 hs5
  have hag5 : AgreesExcept volatileComponents t t5 := (hag4.trans hs5).mono (by simp)
  have hv5 : t5.regValue .rsi = exponentFrameBase s + 0x30 := by
    have hw : t5.regValue .rsi = t4.regValue .rsp + 0x30 := he5.writes
    rw [hw, hp4.frame.rsp]
  obtain ⟨t6, ha6, hr6, he6⟩ :=
    (mov_r64_r64_effect_step 0x1158ba 0x4c 0xf9 (by simp [RexWPrefix]) rfl).advances hr5
      (programText_slice (programLoaded_codeIn hp5.frame.loaded) 0x158ba [0x4c, 0x89, 0xf9]
        (by decide +kernel) rfl) he5.rip (hn 0x158bd (by decide))
  change (movR64R64Effect 0x1158ba 1 15 t5).Holds t5 t6 at he6
  have hs6 : AgreesExcept volatileComponents t5 t6 := he6.agrees.mono (by simp [volatileComponents])
  have hp6 := position_of_registers hp5 hr6 hs6
  have hag6 : AgreesExcept volatileComponents t t6 := (hag5.trans hs6).mono (by simp)
  have hv6 : t6.regValue .rcx = s.regValue .rsi + 32 :=
    he6.writes.trans hp5.parameterPointer
  let am7 : AddrMode := .sib 4 none 0 (.d32 0x2c8)
  have hpre7 : LoadPre 0x1158bd (fun u => am7.addr u 0x1158c5) 8 t6 := by
    refine ⟨he6.rip, ?_⟩
    change MemReadable t6 (t6.regValue .rsp + 0x2c8) 8
    rw [hp6.frame.rsp]
    exact hp6.frame.stack_readable ctx (offset := 0x2c8) (by decide)
  obtain ⟨t7, ha7, hr7, he7⟩ :=
    (mov_r64_m64_effect_step 0x1158bd 0x4c (by simp [RexWPrefix]) 0 am7
      (by constructor <;> decide) rfl rfl).advances hr6
      (programText_slice (programLoaded_codeIn hp6.frame.loaded) 0x158bd
        (0x4c :: 0x8b :: am7.modrm 0 :: am7.tail) (by decide +kernel) (by decide +kernel))
      hpre7 (hn 0x158c5 (by decide))
  change (movR64M64Effect 0x1158bd 8 am7 t6).Holds t6 t7 at he7
  have hs7 : AgreesExcept volatileComponents t6 t7 := he7.agrees.mono (by simp [volatileComponents])
  have hp7 := position_of_registers hp6 hr7 hs7
  have hag7 : AgreesExcept volatileComponents t t7 := (hag6.trans hs7).mono (by simp)
  refine ⟨t7, (((((ha1.trans ha2).trans ha3).trans ha4).trans ha5).trans ha6).trans ha7,
    hp7, he7.rip, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (Operand.reg 6 : Operand 64).read t7 = _
    rw [he7.agrees.read (by simp), he6.agrees.read (by simp)]
    exact hv5
  · change (Operand.reg 2 : Operand 64).read t7 = _
    rw [he7.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp), he4.agrees.read (by simp)]
    exact hv3
  · change (Operand.reg 7 : Operand 64).read t7 = _
    rw [he7.agrees.read (by simp), he6.agrees.read (by simp), he5.agrees.read (by simp)]
    exact hv4
  · exact (he7.agrees.read (n := 64) (r := 1) (by simp)).trans hv6
  · have hw : t7.regValue .r8 = (Operand.mem (t6.regValue .rsp + 0x2c8) : Operand 64).read t6 := he7.writes
    rw [hp6.frame.rsp] at hw
    exact hw.trans hp6.constants.negativeInverse
  · apply montgomeryAt_of_memory _ hacc
    intro a
    exact congrArg (fun m : Ram => m[a]?) (hag7.external (by simp [volatileComponents, Component.Covers]))

end P256.Proofs.Sec1.SquareRoot.ExponentMultiply
