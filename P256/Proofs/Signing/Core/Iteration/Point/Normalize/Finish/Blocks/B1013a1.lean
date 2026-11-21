import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b1013a1Bytes : List UInt8 :=
  [72, 141, 124, 36, 104, 76, 137, 254, 72, 137, 234, 68, 137, 225]

def b1013a1Effect (s : RamState) : Effect :=
  { rip := 0x10d0d3
    writes := [⟨(.reg 7 : Operand 64),stackPtr s+104⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64),(Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64),((Operand.reg 12 : Operand 32).read s).setWidth 64⟩] }

theorem b1013a1_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d0c5)
      (codeRange 0x10d0c5 b1013a1Bytes) (Effect.post b1013a1Effect) := by
  advance_begin (lea_r64_effect_step 0x10d0c5 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd0ca (by decide))
  advance_then (mov_r64_r64_effect_step 0x10d0ca 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d0c5 b1013a1Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd0cd (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10d0cd 0x48 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d0c5 b1013a1Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd0d0 (by decide))⟩
  advance_then (mov_r32_r32_rex_effect_step 0x10d0d0 0x44 0xe1 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d0c5 b1013a1Bytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd0d3 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b1013a1Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b1013a1Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b1013a1Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b1013a1Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks
