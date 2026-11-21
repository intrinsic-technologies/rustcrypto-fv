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

def b1165a5Bytes : List UInt8 :=
  [76, 141, 180, 36, 8, 4, 0, 0, 185, 12, 0, 0, 0, 76, 137, 247, 72, 199, 198, 200, 42, 32, 0]

def b1165a5Effect (s : RamState) : Effect :=
  { rip := 0x10e84c
    writes := [⟨(Operand.reg 14 : Operand 64), stackPtr s + 1032⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 1032⟩,
      ⟨(Operand.reg 6 : Operand 64), 2108104⟩] }

theorem b1165a5_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e835)
      (codeRange 0x10e835 b1165a5Bytes) (Effect.post b1165a5Effect) := by
  advance_begin (lea_r64_effect_step 0x10e835 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 1032)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0xe83d (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10e83d 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10e835 b1165a5Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe842 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10e842 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e835 b1165a5Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe845 (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x10e845 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 2108104)
  case sub => exact codeRange_slice_subset 0x10e835 b1165a5Bytes 16 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xe84c (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b1165a5Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b1165a5Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b1165a5Effect, BitVec.add_zero]
  · x86_norm [b1165a5Effect, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Basepoint.Blocks
