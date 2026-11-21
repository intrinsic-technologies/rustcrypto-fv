import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def b11648eBytes : List UInt8 :=
  [72, 141, 172, 36, 104, 1, 0, 0, 76, 141, 164, 36, 200, 1, 0, 0, 76, 141, 180, 36, 40, 2, 0, 0, 76, 141, 172, 36, 8, 7, 0, 0, 185, 12, 0, 0, 0, 76, 137, 239, 72, 199, 198, 200, 42, 32, 0]

def b11648eEffect (s : RamState) : Effect :=
  { rip := 0x10e74d
    writes := [⟨(Operand.reg 5 : Operand 64), stackPtr s + 360⟩,
      ⟨(Operand.reg 12 : Operand 64), stackPtr s + 456⟩,
      ⟨(Operand.reg 14 : Operand 64), stackPtr s + 552⟩,
      ⟨(Operand.reg 13 : Operand 64), stackPtr s + 1800⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 1800⟩,
      ⟨(Operand.reg 6 : Operand 64), 2108104⟩] }

theorem b11648e_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e71e)
      (codeRange 0x10e71e b11648eBytes) (Effect.post b11648eEffect) := by
  advance_begin (lea_r64_effect_step 0x10e71e 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 360)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xe726 (by decide))
  advance_then (lea_r64_effect_step 0x10e726 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 456)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e71e b11648eBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe72e (by decide))⟩
  advance_then (lea_r64_effect_step 0x10e72e 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 552)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e71e b11648eBytes 16 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe736 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10e736 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 1800)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e71e b11648eBytes 24 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe73e (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10e73e 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10e71e b11648eBytes 32 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe743 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10e743 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e71e b11648eBytes 37 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe746 (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x10e746 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 2108104)
  case sub => exact codeRange_slice_subset 0x10e71e b11648eBytes 40 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe74d (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b11648eEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b11648eEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b11648eEffect, BitVec.add_zero]
  · x86_norm [b11648eEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks
