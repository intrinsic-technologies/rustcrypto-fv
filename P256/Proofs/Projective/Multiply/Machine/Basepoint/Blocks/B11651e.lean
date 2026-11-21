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

def b11651eBytes : List UInt8 :=
  [76, 141, 164, 36, 8, 4, 0, 0, 185, 12, 0, 0, 0, 76, 137, 231, 72, 199, 198, 200, 42, 32, 0]

def b11651eEffect (s : RamState) : Effect :=
  { rip := 0x10e7c5
    writes := [⟨(Operand.reg 12 : Operand 64), stackPtr s + 1032⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 1032⟩,
      ⟨(Operand.reg 6 : Operand 64), 2108104⟩] }

theorem b11651e_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e7ae)
      (codeRange 0x10e7ae b11651eBytes) (Effect.post b11651eEffect) := by
  advance_begin (lea_r64_effect_step 0x10e7ae 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 1032)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xe7b6 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10e7b6 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10e7ae b11651eBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe7bb (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10e7bb 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e7ae b11651eBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe7be (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x10e7be 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 2108104)
  case sub => exact codeRange_slice_subset 0x10e7ae b11651eBytes 16 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe7c5 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b11651eEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b11651eEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b11651eEffect, BitVec.add_zero]
  · x86_norm [b11651eEffect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks
