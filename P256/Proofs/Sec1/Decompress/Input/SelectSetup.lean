import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.MovzxByte
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

def selectSetupBytes : List UInt8 :=
  [0x4c, 0x8d, 0x7c, 0x24, 0x78, 0x48, 0x8d, 0xb4, 0x24, 0xe0, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x94, 0x24, 0x0, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xff, 0x89, 0xe9]

def selectSetupEffect (s : RamState) : Effect :=
  { rip := 0x10fdc7
    writes := [⟨(Operand.reg 15 : Operand 64), stackPtr s+120⟩,
      ⟨(Operand.reg 6 : Operand 64), stackPtr s+224⟩,
      ⟨(Operand.reg 2 : Operand 64), stackPtr s+256⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s+120⟩,
      ⟨(Operand.reg 1 : Operand 64), ((Operand.reg 5 : Operand 64).read s).setWidth 32 |>.setWidth 64⟩] }

theorem selectSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP=0x10fdad) (codeRange 0x10fdad selectSetupBytes)
      (Effect.post selectSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10fdad 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfdb2 (by decide))
  advance_then (lea_r64_effect_step 0x10fdb2 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 224)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fdad selectSetupBytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfdba (by decide))
  advance_then (lea_r64_effect_step 0x10fdba 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 256)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fdad selectSetupBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfdc2 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10fdc2 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fdad selectSetupBytes 21 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfdc5 (by decide))
  advance_then (mov_r32_r32_effect_step 0x10fdc5 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x10fdad selectSetupBytes 24 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfdc7 (by decide))
  advance_finish [selectSetupEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Sec1.Decompress.Input
