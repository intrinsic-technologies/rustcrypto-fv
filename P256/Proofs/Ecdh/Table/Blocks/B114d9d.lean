import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Ecdh.Table.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def b114d9dBytes : List UInt8 :=
  [76, 141, 180, 36, 88, 4, 0, 0, 76, 141, 164, 36, 184, 4, 0, 0, 76, 141, 172, 36, 24, 5, 0, 0, 72, 141, 172, 36, 120, 7, 0, 0, 185, 12, 0, 0, 0, 72, 137, 239, 76, 137, 254]

def b114d9dEffect (s : RamState) : Effect :=
  { rip := 0x100178
    writes := [⟨(Operand.reg 14 : Operand 64), stackPtr s + 1112⟩,
      ⟨(Operand.reg 12 : Operand 64), stackPtr s + 1208⟩,
      ⟨(Operand.reg 13 : Operand 64), stackPtr s + 1304⟩,
      ⟨(Operand.reg 5 : Operand 64), stackPtr s + 1912⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 1912⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem b114d9d_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10014d)
      (codeRange 0x10014d b114d9dBytes) (Effect.post b114d9dEffect) := by
  advance_begin (lea_r64_effect_step 0x10014d 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 1112)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x155 (by decide))
  advance_then (lea_r64_effect_step 0x100155 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 1208)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10014d b114d9dBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x15d (by decide))⟩
  advance_then (lea_r64_effect_step 0x10015d 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 1304)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10014d b114d9dBytes 16 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x165 (by decide))⟩
  advance_then (lea_r64_effect_step 0x100165 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 1912)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10014d b114d9dBytes 24 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x16d (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10016d 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10014d b114d9dBytes 32 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x172 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x100172 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10014d b114d9dBytes 37 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x175 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x100175 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10014d b114d9dBytes 40 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x178 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b114d9dEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b114d9dEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b114d9dEffect, BitVec.add_zero]
  · x86_norm [b114d9dEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Ecdh.Table.Blocks
