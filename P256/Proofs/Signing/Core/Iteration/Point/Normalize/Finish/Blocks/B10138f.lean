import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b10138fBytes : List UInt8 :=
  [185, 9, 0, 0, 0, 76, 137, 255, 72, 199, 198, 240, 36, 32, 0]

def b10138fEffect (s : RamState) : Effect :=
  { rip := 0x10d0c2
    writes := [⟨(.reg 1 : Operand 64),9⟩,
      ⟨(.reg 7 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),2106608⟩] }

theorem b10138f_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d0b3)
      (codeRange 0x10d0b3 b10138fBytes) (Effect.post b10138fEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10d0b3 0xb9 (by decide) 9)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd0b8 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10d0b8 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d0b3 b10138fBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd0bb (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x10d0bb 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x2024f0)
  case sub => exact codeRange_slice_subset 0x10d0b3 b10138fBytes 8 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd0c2 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b10138fEffect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b10138fEffect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b10138fEffect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b10138fEffect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks
