import P256.Proofs.Nonce.Initialize.Prepare.Length.High
import X86Proofs.Instructions.Add.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare.Length

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Nonce.Initialize.Conversions.Bsr
open P256.Proofs.Nonce.Initialize.Conversions.XorImmediate
open P256.Proofs.Nonce.Initialize.Conversions.Neg32

theorem middle_limbs [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x107892)
    (cx : s.regValue .rcx = 0) (dx : s.regValue .rdx = 0) (si : s.regValue .rsi = 0)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 11 s t ∧ ReadyToStep t ∧ t.RIP = 0x1078b7 ∧
      t.regValue .rcx = 0 ∧ t.regValue .rdx = 0 ∧
      AgreesExcept [.reg 9, .reg 1, .reg 6, .reg 2, .flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r32_imm32_rex_effect_step 0x107892 0x41 0xb9 (by simp [RexNoWPrefix]) (by decide) 127).advances ready
      (programText_slice code 0x7892 _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x7898 (by decide)))
  have g1 : AgreesExcept [.reg 9, .rip] s s1 := e1.agrees
  have m1 : s1.external = s.external := g1.external (by simp [Component.Covers])
  obtain ⟨s2, a2, r2, e2⟩ :=
    (bsr_r64_r64_effect_step 0x107898 0x4d 0xcd (by simp [RexWPrefix]) rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0x7898 _ (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x789c (by decide)))
  have g2 : AgreesExcept [.reg 9, .flags, .rip] s1 s2 := e2.agrees
  have m2 : s2.external = s.external := (g2.external (by simp [Component.Covers])).trans m1
  obtain ⟨s3, a3, r3, e3⟩ :=
    (xor_r32_imm8_rex_effect_step 0x10789c 0x41 0xf1 63 (by simp [RexNoWPrefix]) rfl rfl).advances r2
      (programText_slice (code.of_external_eq m2) 0x789c _ (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x78a0 (by decide)))
  have g3 : AgreesExcept [.reg 9, .flags, .rip] s2 s3 := e3.agrees
  have m3 : s3.external = s.external := (g3.external (by simp [Component.Covers])).trans m2
  have in1_4 : s3.regValue .rcx = 0 := (((g1.trans g2).trans g3).read (n := 64) (r := 1) (by simp)).trans cx
  obtain ⟨s4, a4, r4, e4⟩ :=
    (neg_r32_effect_step 0x1078a0 0xd9 rfl rfl).advances r3
      (programText_slice (code.of_external_eq m3) 0x78a0 _ (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x78a2 (by decide)))
  have g4 : AgreesExcept [.reg 1, .flags, .rip] s3 s4 := e4.agrees
  have m4 : s4.external = s.external := (g4.external (by simp [Component.Covers])).trans m3
  have v4 : s4.regValue .rcx = 0 := by
    have h : s4.regValue .rcx = (-(s3.regValue .rcx).setWidth 32).setWidth 64 := e4.writes
    simpa [in1_4] using h
  have in1_5 : s4.regValue .rcx = 0 := v4
  obtain ⟨s5, a5, r5, e5⟩ :=
    (and_r32_r32_rex_effect_step 0x1078a2 0x44 0xc9 (by simp [RexNoWPrefix]) rfl).advances r4
      (programText_slice (code.of_external_eq m4) 0x78a2 _ (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x78a5 (by decide)))
  have g5 : AgreesExcept [.reg 1, .flags, .rip] s4 s5 := e5.agrees
  have m5 : s5.external = s.external := (g5.external (by simp [Component.Covers])).trans m4
  have v5 : s5.regValue .rcx = 0 := by
    have h : s5.regValue .rcx = ((s4.regValue .rcx).setWidth 32 &&& (s4.regValue .r9).setWidth 32).setWidth 64 := e5.writes
    simpa [in1_5] using h
  have in1_6 : s5.regValue .rcx = 0 := v5
  have in6_6 : s5.regValue .rsi = 0 := (((((g1.trans g2).trans g3).trans g4).trans g5).read (n := 64) (r := 6) (by simp)).trans si
  obtain ⟨s6, a6, r6, e6⟩ :=
    (add_r32_r32_effect_step 0x1078a5 0xf1 rfl).advances r5
      (programText_slice (code.of_external_eq m5) 0x78a5 _ (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x78a7 (by decide)))
  have g6 : AgreesExcept [.reg 1, .flags, .rip] s5 s6 := e6.agrees
  have m6 : s6.external = s.external := (g6.external (by simp [Component.Covers])).trans m5
  have v6 : s6.regValue .rcx = 0 := by
    have h : s6.regValue .rcx = ((s5.regValue .rcx).setWidth 32 + (s5.regValue .rsi).setWidth 32).setWidth 64 := e6.writes
    simpa [in1_6, in6_6] using h
  obtain ⟨s7, a7, r7, e7⟩ :=
    (mov_r32_imm32_effect_step 0x1078a7 0xbe (by decide) 127).advances r6
      (programText_slice (code.of_external_eq m6) 0x78a7 _ (by decide +kernel) (by decide +kernel)) e6.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x78ac (by decide)))
  have g7 : AgreesExcept [.reg 6, .rip] s6 s7 := e7.agrees
  have m7 : s7.external = s.external := (g7.external (by simp [Component.Covers])).trans m6
  obtain ⟨s8, a8, r8, e8⟩ :=
    (bsr_r64_r64_effect_step 0x1078ac 0x49 0xf6 (by simp [RexWPrefix]) rfl).advances r7
      (programText_slice (code.of_external_eq m7) 0x78ac _ (by decide +kernel) (by decide +kernel)) e7.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x78b0 (by decide)))
  have g8 : AgreesExcept [.reg 6, .flags, .rip] s7 s8 := e8.agrees
  have m8 : s8.external = s.external := (g8.external (by simp [Component.Covers])).trans m7
  obtain ⟨s9, a9, r9, e9⟩ :=
    (xor_r32_imm8_effect_step 0x1078b0 0xf6 63 rfl rfl).advances r8
      (programText_slice (code.of_external_eq m8) 0x78b0 _ (by decide +kernel) (by decide +kernel)) e8.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x78b3 (by decide)))
  have g9 : AgreesExcept [.reg 6, .flags, .rip] s8 s9 := e9.agrees
  have m9 : s9.external = s.external := (g9.external (by simp [Component.Covers])).trans m8
  have in2_10 : s9.regValue .rdx = 0 := (((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).read (n := 64) (r := 2) (by simp)).trans dx
  obtain ⟨s10, a10, r10, e10⟩ :=
    (neg_r32_effect_step 0x1078b3 0xda rfl rfl).advances r9
      (programText_slice (code.of_external_eq m9) 0x78b3 _ (by decide +kernel) (by decide +kernel)) e9.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x78b5 (by decide)))
  have g10 : AgreesExcept [.reg 2, .flags, .rip] s9 s10 := e10.agrees
  have m10 : s10.external = s.external := (g10.external (by simp [Component.Covers])).trans m9
  have v10 : s10.regValue .rdx = 0 := by
    have h : s10.regValue .rdx = (-(s9.regValue .rdx).setWidth 32).setWidth 64 := e10.writes
    simpa [in2_10] using h
  have in2_11 : s10.regValue .rdx = 0 := v10
  obtain ⟨s11, a11, r11, e11⟩ :=
    (and_r32_r32_effect_step 0x1078b5 0xf2 rfl).advances r10
      (programText_slice (code.of_external_eq m10) 0x78b5 _ (by decide +kernel) (by decide +kernel)) e10.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x78b7 (by decide)))
  have g11 : AgreesExcept [.reg 2, .flags, .rip] s10 s11 := e11.agrees
  have m11 : s11.external = s.external := (g11.external (by simp [Component.Covers])).trans m10
  have v11 : s11.regValue .rdx = 0 := by
    have h : s11.regValue .rdx = ((s10.regValue .rdx).setWidth 32 &&& (s10.regValue .rsi).setWidth 32).setWidth 64 := e11.writes
    simpa [in2_11] using h
  refine ⟨s11, ((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11), r11, e11.rip, ?_, v11, ?_⟩
  · exact (((((g7.trans g8).trans g9).trans g10).trans g11).read (n := 64) (r := 1) (by simp)).trans v6
  · exact ((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).mono (by simp)

end P256.Proofs.Nonce.Initialize.Prepare.Length
