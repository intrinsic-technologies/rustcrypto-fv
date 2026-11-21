import P256.Proofs.Sec1.SquareRoot.Exponent.ReadDigit.State

import P256.Proofs.Common.Instructions.CmovMemory.Effect
import P256.Proofs.Common.Encoding.Serialize.Tail.Selection.Cmov
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmov_r32_r32_effect_step cmov_r32_m32_effect_step)
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_digit_mask [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n : Nat}
    (ctx : ExponentPre s boundary x) (hp : ExponentPosition s t x n)
    (hn : n < 64) (hip : t.RIP = 0x11587f) :
    ∃ u, Advances boundary 6 t u ∧ ReadyToStep u ∧ u.RIP = 0x11589a ∧
      (Operand.reg 1 : Operand 64).read u = (if n = 63 then 3 else 15) ∧
      AgreesExcept [.reg 1, .reg 2, .flags, .rip] t u := by
  have hnext (offset : Nat) (ho : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset offset ho)
  have hc1 : CodeIn (codeRange 0x11587f [0x45, 0x39, 0xee]) t :=
    programText_slice (programLoaded_codeIn hp.frame.loaded) 0x1587f _ (by decide) (by decide +kernel)
  obtain ⟨t1, ha1, hr1, he1⟩ := (cmp_r32_r32_rex_effect_step 0x11587f 0x45 0xee
    (by simp [RexNoWPrefix]) rfl).advances
    (readyToStep hp.frame.machine hp.frame.bindingsSupported) hc1 hip (hnext 0x15882 (by decide))
  have hs1 : AgreesExcept [.flags, .rip] t t1 := he1.agrees
  have hp1 := hp.of_digit_registers hr1 (hs1.mono (by simp [digitReadComponents]))
  have hf1 : (StatusFlags.ofRFLAGS t1.RFLAGS).ZF = decide (n % 16 = 15) := by
    have hf := he1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t1.RFLAGS).ZF =
      (((Operand.reg 14 : Operand 32).read t - (Operand.reg 13 : Operand 32).read t) == 0) at hf
    have hr14 : (Operand.reg 13 : Operand 32).read t = 15#32 := by
      change (t.regValue .r13).setWidth 32 = _
      rw [hp.firstWindow]
      rfl
    rw [hf, hp.window32, hr14]
    exact (show ∀ i : Fin 64, (BitVec.ofNat 32 (i.val % 16) - 15#32 == 0) =
      decide (i.val % 16 = 15) by decide +kernel) ⟨n, hn⟩
  have hc2 : CodeIn (codeRange 0x115882 [0xb9, 15, 0, 0, 0]) t1 :=
    programText_slice (programLoaded_codeIn hp1.frame.loaded) 0x15882 _ (by decide) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ := (mov_r32_imm32_effect_step 0x115882 0xb9 (by decide) 15).advances
    hr1 hc2 he1.rip (hnext 0x15887 (by decide))
  have hs2 : AgreesExcept [.reg 1, .rip] t1 t2 := he2.agrees
  have hp2 := hp1.of_digit_registers hr2 (hs2.mono (by simp [digitReadComponents]))
  have hf2 : (StatusFlags.ofRFLAGS t2.RFLAGS).ZF = decide (n % 16 = 15) := by
    rw [hs2.rflags (by decide) (by decide), hf1]
  have hv2 : (Operand.reg 1 : Operand 64).read t2 = 15 := he2.writes
  have hv2low : (Operand.reg 1 : Operand 32).read t2 = 15#32 := by
    have hh := congrArg (BitVec.setWidth 32) hv2
    exact hh
  have haddr : (AddrMode.sib 4 none 0 (.d32 0x2d8)).addr t2 0x11588f =
      exponentFrameBase s + 0x2d8 := by
    change t2.regValue .rsp + 0x2d8 = _
    rw [hp2.frame.rsp]
  have hread : MemReadable t2
      ((AddrMode.sib 4 none 0 (.d32 0x2d8)).addr t2 0x11588f) 4 := by
    rw [haddr]
    exact hp2.frame.stack_readable ctx (offset := 0x2d8) (len := 4) (by decide)
  have hmask : (Operand.mem ((AddrMode.sib 4 none 0 (.d32 0x2d8)).addr t2 0x11588f) : Operand 32).read t2 = 3 := by
    rw [haddr]
    have hh := congrArg (BitVec.setWidth 32) hp2.constants.initialMask
    change (memLoad t2.external (exponentFrameBase s + 0x2d8) 64).setWidth 32 = _ at hh
    rw [P256.Proofs.Common.Field.SquareRoot.memLoad_setWidth_of_le _ _ (by decide) (by decide)] at hh
    exact hh
  have hc3 : CodeIn (codeRange 0x115887 [0x0f, 0x44, 0x8c, 0x24, 0xd8, 2, 0, 0]) t2 :=
    programText_slice (programLoaded_codeIn hp2.frame.loaded) 0x15887 _ (by decide) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ := (cmov_r32_m32_effect_step 0x115887 0x44 (Or.inr (Or.inl rfl)) 1
      (.sib 4 none 0 (.d32 0x2d8)) (by simp [AddrMode.Valid]) rfl rfl).advances
    hr2 hc3 ⟨he2.rip, hread⟩ (hnext 0x1588f (by decide))
  have hs3 : AgreesExcept [.reg 1, .rip] t2 t3 := he3.agrees
  have hp3 := hp2.of_digit_registers hr3 (hs3.mono (by simp [digitReadComponents]))
  have hv3 : (Operand.reg 1 : Operand 64).read t3 =
      ((if n % 16 = 15 then 3 else 15) : BitVec 64) := by
    have hh := he3.writes
    change (Operand.reg 1 : Operand 64).read t3 =
      (if (StatusFlags.ofRFLAGS t2.RFLAGS).ZF then
        (Operand.mem ((AddrMode.sib 4 none 0 (.d32 0x2d8)).addr t2 0x11588f) : Operand 32).read t2
      else (Operand.reg 1 : Operand 32).read t2).setWidth 64 at hh
    rw [hh, hf2, hmask, hv2low]
    by_cases hcase : n % 16 = 15 <;> simp [hcase]
  have hc4 : CodeIn (codeRange 0x11588f [0x48, 0x39, 0xdd]) t3 :=
    programText_slice (programLoaded_codeIn hp3.frame.loaded) 0x1588f _ (by decide) (by decide +kernel)
  obtain ⟨t4, ha4, hr4, he4⟩ := (cmp_r64_r64_effect_step 0x11588f 0x48 0xdd
    (by constructor <;> rfl) rfl).advances hr3 hc4 he3.rip (hnext 0x15892 (by decide))
  have hs4 : AgreesExcept [.flags, .rip] t3 t4 := he4.agrees
  have hp4 := hp3.of_digit_registers hr4 (hs4.mono (by simp [digitReadComponents]))
  have hf4 : (StatusFlags.ofRFLAGS t4.RFLAGS).ZF = decide (n / 16 = 3) := by
    have hh := he4.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t4.RFLAGS).ZF =
      ((t3.regValue .rbp - t3.regValue .rbx) == 0) at hh
    rw [hh, hp3.word, hp3.firstWord]
    exact (show ∀ i : Fin 64, (BitVec.ofNat 64 (i.val / 16) - 3#64 == 0) =
      decide (i.val / 16 = 3) by decide +kernel) ⟨n, hn⟩
  have hc5 : CodeIn (codeRange 0x115892 [0xba, 15, 0, 0, 0]) t4 :=
    programText_slice (programLoaded_codeIn hp4.frame.loaded) 0x15892 _ (by decide) (by decide +kernel)
  obtain ⟨t5, ha5, hr5, he5⟩ := (mov_r32_imm32_effect_step 0x115892 0xba (by decide) 15).advances
    hr4 hc5 he4.rip (hnext 0x15897 (by decide))
  have hs5 : AgreesExcept [.reg 2, .rip] t4 t5 := he5.agrees
  have hp5 := hp4.of_digit_registers hr5 (hs5.mono (by simp [digitReadComponents]))
  have hf5 : (StatusFlags.ofRFLAGS t5.RFLAGS).ZF = decide (n / 16 = 3) := by
    rw [hs5.rflags (by decide) (by decide), hf4]
  have hv5 : (Operand.reg 2 : Operand 32).read t5 = 15#32 := by
    have hh : (Operand.reg 2 : Operand 64).read t5 = 15 := he5.writes
    exact congrArg (BitVec.setWidth 32) hh
  have hcx5 : (Operand.reg 1 : Operand 32).read t5 =
      ((if n % 16 = 15 then 3 else 15) : BitVec 32) := by
    have hh : (Operand.reg 1 : Operand 64).read t5 =
        ((if n % 16 = 15 then 3 else 15) : BitVec 64) := by
      rw [hs5.read (by decide), hs4.read (by decide), hv3]
    have hl := congrArg (BitVec.setWidth 32) hh
    by_cases hcase : n % 16 = 15
    · rw [ite_eq_left hcase] at hl ⊢
      exact hl
    · rw [ite_eq_right hcase] at hl ⊢
      exact hl
  have hc6 : CodeIn (codeRange 0x115897 [0x0f, 0x45, 0xca]) t5 :=
    programText_slice (programLoaded_codeIn hp5.frame.loaded) 0x15897 _ (by decide) (by decide +kernel)
  obtain ⟨t6, ha6, hr6, he6⟩ := (cmov_r32_r32_effect_step 0x115897 0x45 0xca
    (.inr rfl) (by decide)).advances hr5 hc6 he5.rip (hnext 0x1589a (by decide))
  have hs6 : AgreesExcept [.reg 1, .rip] t5 t6 := he6.agrees
  refine ⟨t6, ((((ha1.trans ha2).trans ha3).trans ha4).trans ha5).trans ha6,
    hr6, he6.rip, ?_, ?_⟩
  · have hh := he6.writes
    change (Operand.reg 1 : Operand 64).read t6 =
      (if !(StatusFlags.ofRFLAGS t5.RFLAGS).ZF then (Operand.reg 2 : Operand 32).read t5
        else (Operand.reg 1 : Operand 32).read t5).setWidth 64 at hh
    rw [hh, hf5, hv5, hcx5]
    have hm : ∀ i : Fin 64,
        ((if !decide (i.val / 16 = 3) then 15#32 else
          if i.val % 16 = 15 then 3 else 15).setWidth 64) =
          (if i.val = 63 then 3 else 15) := by decide +kernel
    exact hm ⟨n, hn⟩
  · exact (((((hs1.trans hs2).trans hs3).trans hs4).trans hs5).trans hs6).mono (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      grind only)

end P256.Proofs.Sec1.SquareRoot
