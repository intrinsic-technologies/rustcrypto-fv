import Sha2.Proofs.Common.Memory.Fill.Prologue.Neg
import Sha2.Proofs.Common.Memory.Copy.Prologue
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple

set_option autoImplicit false

open Sha2.Proofs.Program

open Sha2.Proofs.Common.Instructions (cmovR64R64Effect cmov_r64_r64_effect_step)
open Sha2.Proofs.Common.Machine (boundary_ne_program inProgram_of_textOffset programText_slice)

namespace Sha2.Proofs.Common.Memory.Fill

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Memory Sha2.Proofs.Common.Memory.Fill

theorem alignment [Bindings]
    {s : RamState} {boundary : ReturnBoundary} {n : Nat}
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programSections.toCodeMap s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x10dd28)
    (hn : s.regValue .r8 = BitVec.ofNat 64 n) (bound : n < 2^32) :
    ∃ t, Advances boundary 9 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ t.RIP = 0x10dd44 ∧
      t.regValue .rcx = BitVec.ofNat 64 (min n ((8 - (s.regValue .rdx).toNat % 8) % 8)) ∧
      t.regValue .rsi = BitVec.ofNat 64 ((n - min n ((8 - (s.regValue .rdx).toNat % 8) % 8)) / 8) ∧
      t.regValue .r8 = BitVec.ofNat 64 ((n - min n ((8 - (s.regValue .rdx).toNat % 8) % 8)) % 8) ∧
      AgreesExcept [.reg 1, .reg 6, .reg 8, .flags, .rip] s t := by
  have step1 : StepEffect (fun s => s.RIP = 0x10dd28)
      (codeRange 0x10dd28 [0x89,0xd1]) (movR32R32Effect 0x10dd28 2 1 2) :=
    mov_r32_r32_effect_step _ _ (by decide)
  obtain ⟨s1, ha1, hr1, he1⟩ := step1.advances hready
    (programText_slice hcode 0xdd28 _ (by decide) (by decide +kernel)) hip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd2a (by decide)))
  have hc1 := he1.codeIn
    (Effect.Avoids.of_noMem (by simp [movR32R32Effect, Effect.components, Component.Covers]) _) hcode
  have step2 : StepEffect (fun s => s.RIP = 0x10dd2a)
      (codeRange 0x10dd2a [0xf7,0xd9]) (negEcxEffect 0x10dd2a) :=
    neg_ecx_effect_step _
  obtain ⟨s2, ha2, hr2, he2⟩ := step2.advances hr1
    (programText_slice hc1 0xdd2a _ (by decide) (by decide +kernel)) he1.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd2c (by decide)))
  have hc2 := he2.codeIn
    (Effect.Avoids.of_noMem (by simp [negEcxEffect, Effect.components, Component.Covers]) _) hc1
  have step3 : StepEffect (fun s => s.RIP = 0x10dd2c)
      (codeRange 0x10dd2c [0x83,0xe1,7]) (andR32Imm8Effect 0x10dd2c 3 1 7) :=
    and_r32_imm8_effect_step 0x10dd2c 0xe1 7 (by decide) (by decide)
  obtain ⟨s3, ha3, hr3, he3⟩ := step3.advances hr2
    (programText_slice hc2 0xdd2c _ (by decide) (by decide +kernel)) he2.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd2f (by decide)))
  have hc3 := he3.codeIn
    (Effect.Avoids.of_noMem (by simp [andR32Imm8Effect, Effect.components, Component.Covers]) _) hc2
  have step4 : StepEffect (fun s => s.RIP = 0x10dd2f)
      (codeRange 0x10dd2f [0x49,0x39,0xc8]) (cmpR64R64Effect 0x10dd2f 8 1) :=
    cmp_r64_r64_effect_step _ _ _ (by simp [RexWPrefix]) (by decide)
  obtain ⟨s4, ha4, hr4, he4⟩ := step4.advances hr3
    (programText_slice hc3 0xdd2f _ (by decide) (by decide +kernel)) he3.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd32 (by decide)))
  have hc4 := he4.codeIn
    (Effect.Avoids.of_noMem (by simp [cmpR64R64Effect, Effect.components, Component.Covers]) _) hc3
  have step5 : StepEffect (fun s => s.RIP = 0x10dd32)
      (codeRange 0x10dd32 [0x49,0x0f,0x42,0xc8]) (cmovR64R64Effect 0x10dd32 2 1 8) :=
    cmov_r64_r64_effect_step _ _ _ _ (by simp [RexWPrefix]) (Or.inl rfl) (by decide)
  obtain ⟨s5, ha5, hr5, he5⟩ := step5.advances hr4
    (programText_slice hc4 0xdd32 _ (by decide) (by decide +kernel)) he4.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd36 (by decide)))
  have hc5 := he5.codeIn
    (Effect.Avoids.of_noMem (by simp [cmovR64R64Effect, Effect.components, Component.Covers]) _) hc4
  have step6 : StepEffect (fun s => s.RIP = 0x10dd36)
      (codeRange 0x10dd36 [0x49,0x29,0xc8]) (subR64R64Effect 0x10dd36 8 1) :=
    sub_r64_r64_effect_step _ _ _ (by simp [RexWPrefix]) (by decide)
  obtain ⟨s6, ha6, hr6, he6⟩ := step6.advances hr5
    (programText_slice hc5 0xdd36 _ (by decide) (by decide +kernel)) he5.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd39 (by decide)))
  have hc6 := he6.codeIn
    (Effect.Avoids.of_noMem (by simp [subR64R64Effect, Effect.components, Component.Covers]) _) hc5
  have step7 : StepEffect (fun s => s.RIP = 0x10dd39)
      (codeRange 0x10dd39 [0x4c,0x89,0xc6]) (movR64R64Effect 0x10dd39 6 8) :=
    mov_r64_r64_effect_step _ _ _ (by simp [RexWPrefix]) (by decide)
  obtain ⟨s7, ha7, hr7, he7⟩ := step7.advances hr6
    (programText_slice hc6 0xdd39 _ (by decide) (by decide +kernel)) he6.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd3c (by decide)))
  have hc7 := he7.codeIn
    (Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components, Component.Covers]) _) hc6
  have step8 : StepEffect (fun s => s.RIP = 0x10dd3c)
      (codeRange 0x10dd3c [0x48,0xc1,0xee,3]) (shrR64Effect 0x10dd3c 4 6 3) :=
    shr_r64_imm8_effect_step _ _ _ _ (by simp [RexWPrefix]) (by decide) (by decide)
  obtain ⟨s8, ha8, hr8, he8⟩ := step8.advances hr7
    (programText_slice hc7 0xdd3c _ (by decide) (by decide +kernel)) he7.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd40 (by decide)))
  have hc8 := he8.codeIn
    (Effect.Avoids.of_noMem (by simp [shrR64Effect, Effect.components, Component.Covers]) _) hc7
  have step9 : StepEffect (fun s => s.RIP = 0x10dd40)
      (codeRange 0x10dd40 [0x41,0x83,0xe0,7]) (andR32Imm8Effect 0x10dd40 4 8 7) :=
    and_r32_imm8_rex_effect_step 0x10dd40 0x41 0xe0 7 (by simp [RexNoWPrefix]) (by decide) (by decide)
  obtain ⟨s9, ha9, hr9, he9⟩ := step9.advances hr8
    (programText_slice hc8 0xdd40 _ (by decide) (by decide +kernel)) he8.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0xdd44 (by decide)))
  have hc9 := he9.codeIn
    (Effect.Avoids.of_noMem (by simp [andR32Imm8Effect, Effect.components, Component.Covers]) _) hc8
  have hf := he1.agrees.trans (he2.agrees.trans (he3.agrees.trans
    (he4.agrees.trans (he5.agrees.trans (he6.agrees.trans
    (he7.agrees.trans (he8.agrees.trans he9.agrees)))))))
  have hframe : AgreesExcept [.reg 1, .reg 6, .reg 8, .flags, .rip] s s9 :=
    hf.mono (by simp [movR32R32Effect, negEcxEffect, andR32Imm8Effect,
      cmpR64R64Effect, cmovR64R64Effect, subR64R64Effect, movR64R64Effect,
      shrR64Effect, Effect.components])
  have cx1 : s1.regValue .rcx = ((s.regValue .rdx).setWidth 32).setWidth 64 := he1.writes
  have cx2 : s2.regValue .rcx = (-((s1.regValue .rcx).setWidth 32)).setWidth 64 := he2.writes
  have cx3 : s3.regValue .rcx = (((s2.regValue .rcx).setWidth 32) &&& (7 : BitVec 32)).setWidth 64 := he3.writes
  have cx3' : s3.regValue .rcx = BitVec.ofNat 64 ((8 - (s.regValue .rdx).toNat % 8) % 8) := by
    rw [cx3, cx2, cx1]
    simp only [BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
    exact memcpy_alignment_count _
  have r83 : s3.regValue .r8 = BitVec.ofNat 64 n := by
    exact ((he1.agrees.trans (he2.agrees.trans he3.agrees)).read
      (n := 64) (r := 8) (by simp [movR32R32Effect, negEcxEffect, andR32Imm8Effect,
        Effect.components])).trans hn
  have cx4 : s4.regValue .rcx = s3.regValue .rcx := he4.agrees.read (n := 64) (r := 1) (by simp)
  have r84 : s4.regValue .r8 = s3.regValue .r8 := he4.agrees.read (n := 64) (r := 8) (by simp)
  have hcf : (StatusFlags.ofRFLAGS s4.RFLAGS).CF =
      decide ((s3.regValue .r8).toNat < (s3.regValue .rcx).toNat) := he4.flags.1
  have cx5 : s5.regValue .rcx =
      (if (StatusFlags.ofRFLAGS s4.RFLAGS).CF then s4.regValue .r8 else s4.regValue .rcx) := he5.writes
  have cx5' : s5.regValue .rcx = BitVec.ofNat 64 (min n ((8 - (s.regValue .rdx).toNat % 8) % 8)) := by
    rw [cx5, hcf, r83, cx3', cx4, cx3', r84, r83]
    have h8 := Nat.mod_lt (8 - (s.regValue .rdx).toNat % 8) (show 0 < 8 by decide)
    have hn64 : n < 2^64 := by omega
    have hh64 : (8 - (s.regValue .rdx).toNat % 8) % 8 < 2^64 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hh64,
      decide_eq_true_eq]
    by_cases hnhead : n < (8 - (s.regValue .rdx).toNat % 8) % 8
    · simp [hnhead, Nat.min_eq_left (by omega : n ≤ (8 - (s.regValue .rdx).toNat % 8) % 8)]
    · simp [hnhead, Nat.min_eq_right (by omega : (8 - (s.regValue .rdx).toNat % 8) % 8 ≤ n)]
  have r85 : s5.regValue .r8 = BitVec.ofNat 64 n :=
    (he5.agrees.read (n := 64) (r := 8) (by simp [cmovR64R64Effect, Effect.components])).trans
      (r84.trans r83)
  have r86 : s6.regValue .r8 = BitVec.ofNat 64 (n - min n ((8 - (s.regValue .rdx).toNat % 8) % 8)) := by
    have hw : s6.regValue .r8 = s5.regValue .r8 - s5.regValue .rcx := he6.writes
    rw [hw, r85, cx5']
    exact BitVec.ofNat_sub_ofNat_of_le n _ (by omega) (Nat.min_le_left _ _)
  have si7 : s7.regValue .rsi = s6.regValue .r8 := he7.writes
  have si8 : s8.regValue .rsi =
      BitVec.ofNat 64 ((n - min n ((8 - (s.regValue .rdx).toNat % 8) % 8)) / 8) := by
    have hw : s8.regValue .rsi = s7.regValue .rsi >>> 3 := he8.writes
    rw [hw, si7, r86]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have r88 : s8.regValue .r8 = s6.regValue .r8 :=
    (he7.agrees.trans he8.agrees).read (n := 64) (r := 8)
      (by simp [movR64R64Effect, shrR64Effect, Effect.components])
  have r89 : s9.regValue .r8 =
      BitVec.ofNat 64 ((n - min n ((8 - (s.regValue .rdx).toNat % 8) % 8)) % 8) := by
    have hw : s9.regValue .r8 = ((s8.regValue .r8).setWidth 32 &&& (7#32)).setWidth 64 := he9.writes
    rw [hw, r88, r86]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    change (((n - min n ((8 - (s.regValue .rdx).toNat % 8) % 8)) % 18446744073709551616 %
      4294967296) &&& (2^3-1)) % 18446744073709551616 = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have cx9 : s9.regValue .rcx = s5.regValue .rcx :=
    (he6.agrees.trans (he7.agrees.trans (he8.agrees.trans he9.agrees))).read
      (n := 64) (r := 1) (by simp [subR64R64Effect, movR64R64Effect, shrR64Effect,
        andR32Imm8Effect, Effect.components])
  have si9 : s9.regValue .rsi = s8.regValue .rsi :=
    he9.agrees.read (n := 64) (r := 6) (by simp)
  exact ⟨s9, ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans
    (ha6.trans (ha7.trans (ha8.trans ha9))))))), hr9, hc9, he9.rip,
    cx9.trans cx5', si9.trans si8, r89, hframe⟩

end Sha2.Proofs.Common.Memory.Fill
