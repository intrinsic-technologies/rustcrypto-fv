import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b1013b4Bytes : List UInt8 :=
  [72, 141, 188, 36, 136, 0, 0, 0, 72, 141, 180, 36, 80, 5, 0, 0, 72, 141, 148, 36, 48, 2, 0, 0, 68, 137, 225]

def b1013b4Effect (s : RamState) : Effect :=
  { rip := 0x10d0f3
    writes := [⟨(.reg 7 : Operand 64),stackPtr s+136⟩,
      ⟨(.reg 6 : Operand 64),stackPtr s+1360⟩,
      ⟨(.reg 2 : Operand 64),stackPtr s+560⟩,
      ⟨(.reg 1 : Operand 64),((Operand.reg 12 : Operand 32).read s).setWidth 64⟩] }

theorem b1013b4_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d0d8)
      (codeRange 0x10d0d8 b1013b4Bytes) (Effect.post b1013b4Effect) := by
  advance_begin (lea_r64_effect_step 0x10d0d8 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd0e0 (by decide))
  advance_then (lea_r64_effect_step 0x10d0e0 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 1360)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d0d8 b1013b4Bytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd0e8 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10d0e8 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 560)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d0d8 b1013b4Bytes 16 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd0f0 (by decide))⟩
  advance_then (mov_r32_r32_rex_effect_step 0x10d0f0 0x44 0xe1 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d0d8 b1013b4Bytes 24 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd0f3 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b1013b4Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b1013b4Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b1013b4Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b1013b4Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks
