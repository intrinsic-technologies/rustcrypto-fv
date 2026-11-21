import P256.Proofs.Sec1.Affine.Uncompressed.Output.Not
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.MovzxByte

attribute [local x86_compose] notR15bEffect

@[x86_local] theorem not_r15b_local (p : BitVec 64) : Effect.Local (notR15bEffect p) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [notR15bEffect, h.read_reg]
  · intro s
    simp [notR15bEffect, Write.Full, Operand.Full]

def flagsBytes : List UInt8 := [0xf,0xb6,0xe8,0x41,0x89,0xc7,0x41,0xf6,0xd7,0x4c,0x8d,0x74,0x24,0x30,0x48,0x8d,0x84,0x24,0xa8,0x0,0x0,0x0,0xb9,0x9,0x0,0x0,0x0,0x48,0x89,0xc7,0x48,0xc7,0xc6,0xf8,0x2d,0x20,0x0]

def flagsEffect (s : RamState) : Effect :=
  { rip := 0x110c92
    writes := [
      ⟨(.reg 5 : Operand 64), ((Operand.reg 0 : Operand 8).read s).setWidth 64⟩,
      ⟨(.reg 15 : Operand 64), mergeGPR 8
        (~~~((Operand.reg 0 : Operand 8).read s))
        (((Operand.reg 0 : Operand 32).read s).setWidth 64)⟩,
      ⟨(.reg 14 : Operand 64), stackPtr s + 48⟩,
      ⟨(.reg 0 : Operand 64), stackPtr s + 168⟩,
      ⟨(.reg 1 : Operand 64), 9⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 168⟩,
      ⟨(.reg 6 : Operand 64), 0x202df8⟩] }

set_option maxHeartbeats 800000 in
theorem flags_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x110c6d)
      (codeRange 0x110c6d flagsBytes) (Effect.post flagsEffect) := by
  advance_begin (movzx_r32_r8_effect_step 0x110c6d 0xe8 rfl (by decide))
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10c70 (by decide))
  advance_then (mov_r32_r32_rex_effect_step 0x110c70 0x41 0xc7 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x110c6d flagsBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm [notR15bEffect]), Effect.Avoids.of_noMem (by x86_norm; simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10c73 (by decide))⟩
  advance_then (not_r15b_effect_step 0x110c73)
  case sub => exact codeRange_slice_subset 0x110c6d flagsBytes 6 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm [notR15bEffect]), Effect.Avoids.of_noMem (by x86_norm; simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10c76 (by decide))⟩
  advance_then (lea_r64_effect_step 0x110c76 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110c6d flagsBytes 9 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm [notR15bEffect]), Effect.Avoids.of_noMem (by x86_norm; simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10c7b (by decide))⟩
  advance_then (lea_r64_effect_step 0x110c7b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110c6d flagsBytes 14 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm [notR15bEffect]), Effect.Avoids.of_noMem (by x86_norm; simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10c83 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x110c83 0xb9 (by decide) 9)
  case sub => exact codeRange_slice_subset 0x110c6d flagsBytes 22 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm [notR15bEffect]), Effect.Avoids.of_noMem (by x86_norm; simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10c88 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x110c88 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x110c6d flagsBytes 27 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm [notR15bEffect]), Effect.Avoids.of_noMem (by x86_norm; simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10c8b (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x110c8b 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x202df8)
  case sub => exact codeRange_slice_subset 0x110c6d flagsBytes 30 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm [notR15bEffect]), Effect.Avoids.of_noMem (by x86_norm; simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10c92 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [flagsEffect, notR15bEffect]
    repeat constructor <;> rfl
  · x86_norm [flagsEffect, notR15bEffect, stackPtr, gprNumber, rexR, rexB,
      modrmReg, modrmRm, UInt8.toBitVec, BitVec.setWidth_setWidth_of_le]
    repeat constructor
    all_goals simp [Operand.read, BitVec.setWidth_setWidth_of_le, UInt8.toBitVec_ofNat]
  · intro i; cases i <;> x86_norm [flagsEffect, notR15bEffect]
  · x86_norm [flagsEffect, notR15bEffect]

end P256.Proofs.Sec1.Affine.Uncompressed.Output
