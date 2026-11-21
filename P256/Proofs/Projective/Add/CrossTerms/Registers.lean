import P256.Proofs.Projective.Add.Entry
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.CrossTerms

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def leftXYRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xbc, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xff]

def leftXYRegisterEffect (s : RamState) : Effect :=
  { rip := 0x10537b
    writes := [
      ⟨(.reg 15 : Operand 64), stackPtr s + 552⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 552⟩] }

theorem leftXY_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105366)
      (codeRange 0x105366 leftXYRegisterBytes) (Effect.post leftXYRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x105366 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 552)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x536e (by decide))
  advance_then (lea_r64_effect_step 0x10536e 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105366 leftXYRegisterBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5373 (by decide))
  advance_then (lea_r64_effect_step 0x105373 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105366 leftXYRegisterBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5378 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105378 0x4c 0xff (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105366 leftXYRegisterBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x537b (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [leftXYRegisterEffect]
  · x86_norm [leftXYRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [leftXYRegisterEffect]
  · x86_norm [leftXYRegisterEffect]

def rightXYRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xac, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xef]

def rightXYRegisterEffect (s : RamState) : Effect :=
  { rip := 0x1053dc
    writes := [
      ⟨(.reg 13 : Operand 64), stackPtr s + 136⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 136⟩] }

theorem rightXY_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1053c7)
      (codeRange 0x1053c7 rightXYRegisterBytes) (Effect.post rightXYRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x1053c7 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x53cf (by decide))
  advance_then (lea_r64_effect_step 0x1053cf 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1053c7 rightXYRegisterBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53d4 (by decide))
  advance_then (lea_r64_effect_step 0x1053d4 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1053c7 rightXYRegisterBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53d9 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1053d9 0x4c 0xef (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1053c7 rightXYRegisterBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53dc (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [rightXYRegisterEffect]
  · x86_norm [rightXYRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [rightXYRegisterEffect]
  · x86_norm [rightXYRegisterEffect]

def productXYRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xa4, 0x24, 0xc8, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x4c, 0x89, 0xfe, 0x4c, 0x89, 0xea]

def productXYRegisterEffect (s : RamState) : Effect :=
  { rip := 0x1053f2
    writes := [
      ⟨(.reg 12 : Operand 64), stackPtr s + 200⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 200⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩] }

theorem productXY_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1053e1)
      (codeRange 0x1053e1 productXYRegisterBytes) (Effect.post productXYRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x1053e1 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x53e9 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1053e9 0x4c 0xe7 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1053e1 productXYRegisterBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53ec (by decide))
  advance_then (mov_r64_r64_effect_step 0x1053ec 0x4c 0xfe (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1053e1 productXYRegisterBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53ef (by decide))
  advance_then (mov_r64_r64_effect_step 0x1053ef 0x4c 0xea (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1053e1 productXYRegisterBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53f2 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [productXYRegisterEffect]
  · x86_norm [productXYRegisterEffect]
    all_goals simp [Operand.read_reg64, gprNumber, rexR, modrmReg]
  · intro i
    cases i <;> x86_norm [productXYRegisterEffect]
  · x86_norm [productXYRegisterEffect]

def sumXXYYRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xbc, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xff]

def sumXXYYRegisterEffect (s : RamState) : Effect :=
  { rip := 0x105468
    writes := [
      ⟨(.reg 15 : Operand 64), stackPtr s + 136⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 136⟩] }

theorem sumXXYY_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105453)
      (codeRange 0x105453 sumXXYYRegisterBytes) (Effect.post sumXXYYRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x105453 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x545b (by decide))
  advance_then (lea_r64_effect_step 0x10545b 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105453 sumXXYYRegisterBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5460 (by decide))
  advance_then (lea_r64_effect_step 0x105460 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105453 sumXXYYRegisterBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5465 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105465 0x4c 0xff (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105453 sumXXYYRegisterBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5468 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [sumXXYYRegisterEffect]
  · x86_norm [sumXXYYRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [sumXXYYRegisterEffect]
  · x86_norm [sumXXYYRegisterEffect]

def xyRegisterBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0xe8, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xe6, 0x4c, 0x89, 0xfa]

def xyRegisterEffect (s : RamState) : Effect :=
  { rip := 0x10547b
    writes := [
      ⟨(.reg 7 : Operand 64), stackPtr s + 232⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem xy_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10546d)
      (codeRange 0x10546d xyRegisterBytes) (Effect.post xyRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x10546d 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 232)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5475 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105475 0x4c 0xe6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10546d xyRegisterBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5478 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105478 0x4c 0xfa (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10546d xyRegisterBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x547b (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [xyRegisterEffect]
  · x86_norm [xyRegisterEffect]
    all_goals simp [Operand.read_reg64, gprNumber, rexR, modrmReg]
  · intro i
    cases i <;> x86_norm [xyRegisterEffect]
  · x86_norm [xyRegisterEffect]

def leftYZRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xbc, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xff]

def leftYZRegisterEffect (s : RamState) : Effect :=
  { rip := 0x1054dd
    writes := [
      ⟨(.reg 15 : Operand 64), stackPtr s + 552⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 552⟩] }

theorem leftYZ_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1054c8)
      (codeRange 0x1054c8 leftYZRegisterBytes) (Effect.post leftYZRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x1054c8 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 552)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x54d0 (by decide))
  advance_then (lea_r64_effect_step 0x1054d0 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1054c8 leftYZRegisterBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x54d5 (by decide))
  advance_then (lea_r64_effect_step 0x1054d5 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1054c8 leftYZRegisterBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x54da (by decide))
  advance_then (mov_r64_r64_effect_step 0x1054da 0x4c 0xff (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1054c8 leftYZRegisterBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x54dd (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [leftYZRegisterEffect]
  · x86_norm [leftYZRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [leftYZRegisterEffect]
  · x86_norm [leftYZRegisterEffect]

def rightYZRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xac, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xef]

def rightYZRegisterEffect (s : RamState) : Effect :=
  { rip := 0x10553f
    writes := [
      ⟨(.reg 13 : Operand 64), stackPtr s + 136⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 136⟩] }

theorem rightYZ_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10552a)
      (codeRange 0x10552a rightYZRegisterBytes) (Effect.post rightYZRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x10552a 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5532 (by decide))
  advance_then (lea_r64_effect_step 0x105532 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10552a rightYZRegisterBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5537 (by decide))
  advance_then (lea_r64_effect_step 0x105537 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10552a rightYZRegisterBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x553c (by decide))
  advance_then (mov_r64_r64_effect_step 0x10553c 0x4c 0xef (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10552a rightYZRegisterBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x553f (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [rightYZRegisterEffect]
  · x86_norm [rightYZRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [rightYZRegisterEffect]
  · x86_norm [rightYZRegisterEffect]

def productYZRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xa4, 0x24, 0xc8, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x4c, 0x89, 0xfe, 0x4c, 0x89, 0xea]

def productYZRegisterEffect (s : RamState) : Effect :=
  { rip := 0x105555
    writes := [
      ⟨(.reg 12 : Operand 64), stackPtr s + 200⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 200⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩] }

theorem productYZ_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105544)
      (codeRange 0x105544 productYZRegisterBytes) (Effect.post productYZRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x105544 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x554c (by decide))
  advance_then (mov_r64_r64_effect_step 0x10554c 0x4c 0xe7 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105544 productYZRegisterBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x554f (by decide))
  advance_then (mov_r64_r64_effect_step 0x10554f 0x4c 0xfe (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105544 productYZRegisterBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5552 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105552 0x4c 0xea (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105544 productYZRegisterBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5555 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [productYZRegisterEffect]
  · x86_norm [productYZRegisterEffect]
    all_goals simp [Operand.read_reg64, gprNumber, rexR, modrmReg]
  · intro i
    cases i <;> x86_norm [productYZRegisterEffect]
  · x86_norm [productYZRegisterEffect]

def sumYYZZRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xbc, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x8, 0x48, 0x8d, 0x54, 0x24, 0x28, 0x4c, 0x89, 0xff]

def sumYYZZRegisterEffect (s : RamState) : Effect :=
  { rip := 0x1055ce
    writes := [
      ⟨(.reg 15 : Operand 64), stackPtr s + 136⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 136⟩] }

theorem sumYYZZ_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1055b9)
      (codeRange 0x1055b9 sumYYZZRegisterBytes) (Effect.post sumYYZZRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x1055b9 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x55c1 (by decide))
  advance_then (lea_r64_effect_step 0x1055c1 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1055b9 sumYYZZRegisterBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x55c6 (by decide))
  advance_then (lea_r64_effect_step 0x1055c6 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1055b9 sumYYZZRegisterBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x55cb (by decide))
  advance_then (mov_r64_r64_effect_step 0x1055cb 0x4c 0xff (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1055b9 sumYYZZRegisterBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x55ce (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [sumYYZZRegisterEffect]
  · x86_norm [sumYYZZRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [sumYYZZRegisterEffect]
  · x86_norm [sumYYZZRegisterEffect]

def yzRegisterBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x8, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xe6, 0x4c, 0x89, 0xfa]

def yzRegisterEffect (s : RamState) : Effect :=
  { rip := 0x1055e1
    writes := [
      ⟨(.reg 7 : Operand 64), stackPtr s + 264⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem yz_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1055d3)
      (codeRange 0x1055d3 yzRegisterBytes) (Effect.post yzRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x1055d3 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 264)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x55db (by decide))
  advance_then (mov_r64_r64_effect_step 0x1055db 0x4c 0xe6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1055d3 yzRegisterBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x55de (by decide))
  advance_then (mov_r64_r64_effect_step 0x1055de 0x4c 0xfa (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1055d3 yzRegisterBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x55e1 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [yzRegisterEffect]
  · x86_norm [yzRegisterEffect]
    all_goals simp [Operand.read_reg64, gprNumber, rexR, modrmReg]
  · intro i
    cases i <;> x86_norm [yzRegisterEffect]
  · x86_norm [yzRegisterEffect]

def leftXZRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xbc, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xff]

def leftXZRegisterEffect (s : RamState) : Effect :=
  { rip := 0x105642
    writes := [
      ⟨(.reg 15 : Operand 64), stackPtr s + 552⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 552⟩] }

theorem leftXZ_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10562d)
      (codeRange 0x10562d leftXZRegisterBytes) (Effect.post leftXZRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x10562d 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 552)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5635 (by decide))
  advance_then (lea_r64_effect_step 0x105635 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10562d leftXZRegisterBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x563a (by decide))
  advance_then (lea_r64_effect_step 0x10563a 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10562d leftXZRegisterBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x563f (by decide))
  advance_then (mov_r64_r64_effect_step 0x10563f 0x4c 0xff (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10562d leftXZRegisterBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5642 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [leftXZRegisterEffect]
  · x86_norm [leftXZRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [leftXZRegisterEffect]
  · x86_norm [leftXZRegisterEffect]

def rightXZRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xa4, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xe7]

def rightXZRegisterEffect (s : RamState) : Effect :=
  { rip := 0x1056a3
    writes := [
      ⟨(.reg 12 : Operand 64), stackPtr s + 136⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 136⟩] }

theorem rightXZ_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10568e)
      (codeRange 0x10568e rightXZRegisterBytes) (Effect.post rightXZRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x10568e 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5696 (by decide))
  advance_then (lea_r64_effect_step 0x105696 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10568e rightXZRegisterBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x569b (by decide))
  advance_then (lea_r64_effect_step 0x10569b 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10568e rightXZRegisterBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x56a0 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1056a0 0x4c 0xe7 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10568e rightXZRegisterBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x56a3 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [rightXZRegisterEffect]
  · x86_norm [rightXZRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [rightXZRegisterEffect]
  · x86_norm [rightXZRegisterEffect]

def productXZRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xb4, 0x24, 0xc8, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf7, 0x4c, 0x89, 0xfe, 0x4c, 0x89, 0xe2]

def productXZRegisterEffect (s : RamState) : Effect :=
  { rip := 0x1056b9
    writes := [
      ⟨(.reg 14 : Operand 64), stackPtr s + 200⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 200⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩] }

theorem productXZ_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1056a8)
      (codeRange 0x1056a8 productXZRegisterBytes) (Effect.post productXZRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x1056a8 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x56b0 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1056b0 0x4c 0xf7 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1056a8 productXZRegisterBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x56b3 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1056b3 0x4c 0xfe (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1056a8 productXZRegisterBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x56b6 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1056b6 0x4c 0xe2 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1056a8 productXZRegisterBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x56b9 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [productXZRegisterEffect]
  · x86_norm [productXZRegisterEffect]
    all_goals simp [Operand.read_reg64, gprNumber, rexR, modrmReg]
  · intro i
    cases i <;> x86_norm [productXZRegisterEffect]
  · x86_norm [productXZRegisterEffect]

def sumXXZZRegisterBytes : List UInt8 :=
  [0x4c, 0x8d, 0xbc, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xff]

def sumXXZZRegisterEffect (s : RamState) : Effect :=
  { rip := 0x105726
    writes := [
      ⟨(.reg 15 : Operand 64), stackPtr s + 136⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 136⟩] }

theorem sumXXZZ_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105711)
      (codeRange 0x105711 sumXXZZRegisterBytes) (Effect.post sumXXZZRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x105711 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5719 (by decide))
  advance_then (lea_r64_effect_step 0x105719 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105711 sumXXZZRegisterBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x571e (by decide))
  advance_then (lea_r64_effect_step 0x10571e 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105711 sumXXZZRegisterBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5723 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105723 0x4c 0xff (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105711 sumXXZZRegisterBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5726 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [sumXXZZRegisterEffect]
  · x86_norm [sumXXZZRegisterEffect]
    all_goals simp [stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [sumXXZZRegisterEffect]
  · x86_norm [sumXXZZRegisterEffect]

def xzRegisterBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x28, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xf6, 0x4c, 0x89, 0xfa]

def xzRegisterEffect (s : RamState) : Effect :=
  { rip := 0x105739
    writes := [
      ⟨(.reg 7 : Operand 64), stackPtr s + 296⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem xz_registers [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10572b)
      (codeRange 0x10572b xzRegisterBytes) (Effect.post xzRegisterEffect) := by
  advance_begin (lea_r64_effect_step 0x10572b 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 296)) (by decide) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5733 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105733 0x4c 0xf6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10572b xzRegisterBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5736 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105736 0x4c 0xfa (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10572b xzRegisterBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5739 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [xzRegisterEffect]
  · x86_norm [xzRegisterEffect]
    all_goals simp [Operand.read_reg64, gprNumber, rexR, modrmReg]
  · intro i
    cases i <;> x86_norm [xzRegisterEffect]
  · x86_norm [xzRegisterEffect]

end P256.Proofs.Projective.Add.CrossTerms
