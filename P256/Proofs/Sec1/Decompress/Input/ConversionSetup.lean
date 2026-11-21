import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def conversionSetupBytes : List UInt8 :=
  [0x49,0x89,0xe7,0x48,0x8d,0x74,0x24,0x50,0x41,0xb8,0x1,0x0,0x0,0x0,0x4c,0x89,0xff,0x48,0xc7,0xc2,0xc8,0x2d,0x20,0x0,0x48,0xc7,0xc1,0x88,0x2d,0x20,0x0]

def conversionSetupEffect (s : RamState) : Effect :=
  { rip := 0x10fcef
    writes := [⟨(Operand.reg 15 : Operand 64), stackPtr s⟩,
      ⟨(Operand.reg 6 : Operand 64), stackPtr s + 80⟩,
      ⟨(Operand.reg 8 : Operand 64), 1⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s⟩,
      ⟨(Operand.reg 2 : Operand 64), 0x202dc8⟩,
      ⟨(Operand.reg 1 : Operand 64), 0x202d88⟩] }

theorem conversion_setup_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fcd0)
      (codeRange 0x10fcd0 conversionSetupBytes) (Effect.post conversionSetupEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10fcd0 0x49 0xe7
    (by unfold RexWPrefix; decide +kernel) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfcd3 (by decide))
  advance_then (lea_r64_effect_step 0x10fcd3 0x48
    (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 80))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fcd0 conversionSetupBytes 3 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfcd8 (by decide))
  advance_then (mov_r32_imm32_rex_effect_step 0x10fcd8 0x41 0xb8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) 1)
  case sub => exact codeRange_slice_subset 0x10fcd0 conversionSetupBytes 8 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfcde (by decide))
  advance_then (mov_r64_r64_effect_step 0x10fcde 0x4c 0xff
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fcd0 conversionSetupBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfce1 (by decide))
  advance_then (mov_r64_imm32_effect_step 0x10fce1 0x48 0xc2
    (by unfold RexWPrefix; decide +kernel) rfl rfl 0x202dc8)
  case sub => exact codeRange_slice_subset 0x10fcd0 conversionSetupBytes 17 7
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfce8 (by decide))
  advance_then (mov_r64_imm32_effect_step 0x10fce8 0x48 0xc1
    (by unfold RexWPrefix; decide +kernel) rfl rfl 0x202d88)
  case sub => exact codeRange_slice_subset 0x10fcd0 conversionSetupBytes 24 7
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfcef (by decide))
  advance_finish [conversionSetupEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Sec1.Decompress.Input
