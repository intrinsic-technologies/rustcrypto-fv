import P256.Proofs.Sec1.SquareRoot.SelectSetup

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Middle

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def parameterSetupBytes : List UInt8 := [0x4c,0x8d,0xbc,0x24,0x70,0x1,0x0,0x0,0xb9,0xe,0x0,0x0,0x0,0x4c,0x89,0xff,0x48,0xc7,0xc6,0x28,0x2f,0x20,0x0]

def parameterSetupEffect (s : RamState) : Effect :=
  { rip := 0x1144a6
    writes := [⟨(.reg 15 : Operand 64), (.reg 4 : Operand 64).read s + 368⟩,
      ⟨(.reg 1 : Operand 64),14⟩,
      ⟨(.reg 7 : Operand 64), (.reg 4 : Operand 64).read s + 368⟩,
      ⟨(.reg 6 : Operand 64),0x202f28⟩] }

theorem parameterSetup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x11448f parameterSetupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1448f parameterSetupBytes
    (by decide) (by decide +kernel)

theorem parameterSetup_run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x11448f) (codeRange 0x11448f parameterSetupBytes)
      (Effect.post parameterSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x11448f 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 368)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x14497 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x114497 0xb9 (by decide +kernel) 14)
  case sub => exact codeRange_slice_subset 0x11448f parameterSetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1449c (by decide))
  advance_then (mov_r64_r64_effect_step 0x11449c 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11448f parameterSetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1449f (by decide))
  advance_then (mov_r64_imm32_effect_step 0x11449f 0x48 0xc6 (by simp [RexWPrefix]) (by decide) (by decide) 0x202f28)
  case sub => exact codeRange_slice_subset 0x11448f parameterSetupBytes 16 7
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144a6 (by decide))
  advance_finish [parameterSetupEffect, gprNumber, rexR, rexB, modrmReg, modrmRm]

def wideSetupBytes : List UInt8 := [0x4c,0x8d,0xa4,0x24,0xe0,0x1,0x0,0x0,0xba,0x4,0x0,0x0,0x0,0x4c,0x89,0xe7,0x4c,0x89,0xf6]

def wideSetupEffect (s : RamState) : Effect :=
  { rip := 0x1144f0
    writes := [⟨(.reg 12 : Operand 64), (.reg 4 : Operand 64).read s + 480⟩,
      ⟨(.reg 2 : Operand 64),4⟩,
      ⟨(.reg 7 : Operand 64), (.reg 4 : Operand 64).read s + 480⟩,
      ⟨(.reg 6 : Operand 64), (.reg 14 : Operand 64).read s⟩] }

theorem wideSetup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1144dd wideSetupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x144dd wideSetupBytes
    (by decide) (by decide +kernel)

theorem wideSetup_run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1144dd) (codeRange 0x1144dd wideSetupBytes)
      (Effect.post wideSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x1144dd 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 480)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x144e5 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1144e5 0xba (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x1144dd wideSetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144ea (by decide))
  advance_then (mov_r64_r64_effect_step 0x1144ea 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1144dd wideSetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144ed (by decide))
  advance_then (mov_r64_r64_effect_step 0x1144ed 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1144dd wideSetupBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144f0 (by decide))
  advance_finish [wideSetupEffect, gprNumber, rexR, rexB, modrmReg, modrmRm]

def reductionSetupBytes : List UInt8 := [0x48,0x8d,0x7c,0x24,0x30,0xb9,0x1,0x0,0x0,0x0,0x4c,0x89,0xe6,0x4c,0x89,0xfa]

def reductionSetupEffect (s : RamState) : Effect :=
  { rip := 0x114505
    writes := [⟨(.reg 7 : Operand 64), (.reg 4 : Operand 64).read s + 48⟩,
      ⟨(.reg 1 : Operand 64),1⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 15 : Operand 64).read s⟩] }

theorem reductionSetup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1144f5 reductionSetupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x144f5 reductionSetupBytes
    (by decide) (by decide +kernel)

theorem reductionSetup_run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1144f5) (codeRange 0x1144f5 reductionSetupBytes)
      (Effect.post reductionSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x1144f5 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x144fa (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1144fa 0xb9 (by decide +kernel) 1)
  case sub => exact codeRange_slice_subset 0x1144f5 reductionSetupBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144ff (by decide))
  advance_then (mov_r64_r64_effect_step 0x1144ff 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1144f5 reductionSetupBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14502 (by decide))
  advance_then (mov_r64_r64_effect_step 0x114502 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1144f5 reductionSetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14505 (by decide))
  advance_finish [reductionSetupEffect, gprNumber, rexR, rexB, modrmReg, modrmRm]

end P256.Proofs.Sec1.SquareRoot.Middle
