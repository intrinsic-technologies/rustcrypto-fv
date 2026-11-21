import P256.Proofs.Projective.Add.Entry
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Products

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def xxRegisterBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x48, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8]

def xxRegisterEffect (s : RamState) : Effect :=
  { rip := 0x10525c
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 8⟩] }

theorem xx_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10524d)
      (codeRange 0x10524d xxRegisterBytes) (Effect.post xxRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x10524d 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5252 (by decide))
  advance_then (lea_r64_effect_step 0x105252 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10524d xxRegisterBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5257 (by decide))
  advance_then (lea_r64_effect_step 0x105257 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10524d xxRegisterBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x525c (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [xxRegisterEffect]
  · x86_norm [xxRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i; cases i <;> x86_norm [xxRegisterEffect]
  · x86_norm [xxRegisterEffect]

def yyRegisterBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8]

def yyRegisterEffect (s : RamState) : Effect :=
  { rip := 0x1052bb
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 168⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 8⟩] }

theorem yy_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1052a9)
      (codeRange 0x1052a9 yyRegisterBytes) (Effect.post yyRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x1052a9 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x52b1 (by decide))
  advance_then (lea_r64_effect_step 0x1052b1 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1052a9 yyRegisterBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x52b6 (by decide))
  advance_then (lea_r64_effect_step 0x1052b6 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1052a9 yyRegisterBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x52bb (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [yyRegisterEffect]
  · x86_norm [yyRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i; cases i <;> x86_norm [yyRegisterEffect]
  · x86_norm [yyRegisterEffect]

def zzRegisterBytes : List UInt8 :=
  [0x48, 0x8d, 0x6c, 0x24, 0x68, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x48, 0x89, 0xef]

def zzRegisterEffect (s : RamState) : Effect :=
  { rip := 0x10531a
    writes := [⟨(.reg 5 : Operand 64), stackPtr s + 104⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 104⟩] }

theorem zz_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105308)
      (codeRange 0x105308 zzRegisterBytes) (Effect.post zzRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x105308 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x530d (by decide))
  advance_then (lea_r64_effect_step 0x10530d 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105308 zzRegisterBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5312 (by decide))
  advance_then (lea_r64_effect_step 0x105312 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105308 zzRegisterBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5317 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105317 0x48 0xef (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105308 zzRegisterBytes 15 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x531a (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [zzRegisterEffect]
  · x86_norm [zzRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i; cases i <;> x86_norm [zzRegisterEffect]
  · x86_norm [zzRegisterEffect]

end P256.Proofs.Projective.Add.Products
