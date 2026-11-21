import P256.Proofs.Common.Memory.Fill.Prologue.ZeroProduct.Movzx
import P256.Proofs.Common.Instructions.Imul
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (imulR64R64Effect imul_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programText_slice)

namespace P256.Proofs.Program.Fill

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Memory.Fill

theorem zeroProduct [Bindings]
    {s : RamState} {boundary : ReturnBoundary} {n : Nat}
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programSections.toCodeMap s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x11c810)
    (hzero : (s.regValue .rsi).setWidth 32 = 0) (hn : s.regValue .rdx = BitVec.ofNat 64 n) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ t.RIP = 0x11c828 ∧
      t.regValue .rax = 0 ∧ t.regValue .rdx = s.regValue .rdi ∧
      t.regValue .r8 = BitVec.ofNat 64 n ∧
      AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 8, .flags, .rip] s t := by
  have step1 : StepEffect (fun s => s.RIP = 0x11c810)
      (codeRange 0x11c810 [0x49,0x89,0xd0]) (movR64R64Effect 0x11c810 8 2) :=
    mov_r64_r64_effect_step _ _ _ (by simp [RexWPrefix]) (by decide)
  obtain ⟨s1, ha1, hr1, he1⟩ := step1.advances hready
    (programText_slice hcode 0x1c810 _ (by decide) (by decide +kernel)) hip
    (boundary_ne_program hout (inProgram_of_textOffset 0x1c813 (by decide)))
  have hc1 := he1.codeIn
    (Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components, Component.Covers]) _) hcode
  have step2 : StepEffect (fun s => s.RIP = 0x11c813)
      (codeRange 0x11c813 [0x48,0x89,0xfa]) (movR64R64Effect 0x11c813 2 7) :=
    mov_r64_r64_effect_step _ _ _ (by simp [RexWPrefix]) (by decide)
  obtain ⟨s2, ha2, hr2, he2⟩ := step2.advances hr1
    (programText_slice hc1 0x1c813 _ (by decide) (by decide +kernel)) he1.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0x1c816 (by decide)))
  have hc2 := he2.codeIn
    (Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components, Component.Covers]) _) hc1
  have step3 : StepEffect (fun s => s.RIP = 0x11c816)
      (codeRange 0x11c816 [0x40,0x0f,0xb6,0xce]) (movzxEcxsilEffect 0x11c816) :=
    movzx_ecx_sil_effect_step _
  obtain ⟨s3, ha3, hr3, he3⟩ := step3.advances hr2
    (programText_slice hc2 0x1c816 _ (by decide) (by decide +kernel)) he2.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0x1c81a (by decide)))
  have hc3 := he3.codeIn
    (Effect.Avoids.of_noMem (by simp [movzxEcxsilEffect, Effect.components, Component.Covers]) _) hc2
  have step4 : StepEffect (fun s => s.RIP = 0x11c81a)
      (codeRange 0x11c81a [0x48,0xb8,1,1,1,1,1,1,1,1]) (movR64Imm64Effect 0x11c81a 0 0x0101010101010101) :=
    mov_r64_imm64_effect_step 0x11c81a 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x0101010101010101
  obtain ⟨s4, ha4, hr4, he4⟩ := step4.advances hr3
    (programText_slice hc3 0x1c81a _ (by decide) (by decide +kernel)) he3.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0x1c824 (by decide)))
  have hc4 := he4.codeIn
    (Effect.Avoids.of_noMem (by simp [movR64Imm64Effect, Effect.components, Component.Covers]) _) hc3
  have step5 : StepEffect (fun s => s.RIP = 0x11c824)
      (codeRange 0x11c824 [0x48,0x0f,0xaf,0xc1]) (imulR64R64Effect 0x11c824 0 1) :=
    imul_r64_r64_effect_step _ _ _ (by simp [RexWPrefix]) (by decide)
  obtain ⟨s5, ha5, hr5, he5⟩ := step5.advances hr4
    (programText_slice hc4 0x1c824 _ (by decide) (by decide +kernel)) he4.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0x1c828 (by decide)))
  have hc5 := he5.codeIn
    (Effect.Avoids.of_noMem (by simp [imulR64R64Effect, Effect.components, Component.Covers]) _) hc4
  have hf := he1.agrees.trans (he2.agrees.trans (he3.agrees.trans
    (he4.agrees.trans he5.agrees)))
  have hframe : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 8, .flags, .rip] s s5 :=
    hf.mono (by simp [movR64R64Effect, movzxEcxsilEffect, movR64Imm64Effect,
      imulR64R64Effect, Effect.components])
  have r81 : s1.regValue .r8 = s.regValue .rdx := he1.writes
  have r85 : s5.regValue .r8 = BitVec.ofNat 64 n :=
    ((he2.agrees.trans (he3.agrees.trans (he4.agrees.trans he5.agrees))).read
      (n := 64) (r := 8) (by simp [movR64R64Effect, movzxEcxsilEffect,
        movR64Imm64Effect, imulR64R64Effect, Effect.components])).trans (r81.trans hn)
  have dx2 : s2.regValue .rdx = s1.regValue .rdi := he2.writes
  have di1 : s1.regValue .rdi = s.regValue .rdi :=
    he1.agrees.read (n := 64) (r := 7) (by simp)
  have dx5 : s5.regValue .rdx = s.regValue .rdi :=
    ((he3.agrees.trans (he4.agrees.trans he5.agrees)).read
      (n := 64) (r := 2) (by simp [movzxEcxsilEffect, movR64Imm64Effect,
        imulR64R64Effect, Effect.components])).trans (dx2.trans di1)
  have si2 : s2.regValue .rsi = s.regValue .rsi :=
    (he1.agrees.trans he2.agrees).read (n := 64) (r := 6) (by simp)
  have hz8 : (s.regValue .rsi).setWidth 8 = 0 := by
    have hh := congrArg (BitVec.setWidth 8) hzero
    rw [BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)] at hh
    exact hh
  have cx3 : s3.regValue .rcx = 0 := by
    have hw : s3.regValue .rcx = ((s2.regValue .rsi).setWidth 8).setWidth 64 := he3.writes
    rw [hw, si2, hz8]
    rfl
  have cx4 : s4.regValue .rcx = 0 :=
    (he4.agrees.read (n := 64) (r := 1) (by simp)).trans cx3
  have ax5 : s5.regValue .rax = 0 := by
    have hw : s5.regValue .rax = s4.regValue .rax * s4.regValue .rcx := he5.writes
    rw [hw, cx4]
    exact BitVec.mul_zero
  exact ⟨s5, ha1.trans (ha2.trans (ha3.trans (ha4.trans ha5))),
    hr5, hc5, he5.rip, ax5, dx5, r85, hframe⟩

end P256.Proofs.Program.Fill
