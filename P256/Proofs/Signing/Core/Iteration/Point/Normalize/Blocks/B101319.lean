import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b101319Bytes : List UInt8 :=
  [72, 141, 188, 36, 144, 1, 0, 0, 76, 137, 246, 72, 137, 234, 72, 141, 172, 36, 16, 2, 0, 0]

def b101319Effect (s : RamState) : Effect :=
  { rip := 0x10d059
    writes := [⟨(.reg 7 : Operand 64),stackPtr s+400⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64),(Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.reg 5 : Operand 64),stackPtr s+528⟩] }

theorem b101319_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d043)
      (codeRange 0x10d043 b101319Bytes) (Effect.post b101319Effect) := by
  advance_begin (lea_r64_effect_step 0x10d043 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 400)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd04b (by decide))
  advance_then (mov_r64_r64_effect_step 0x10d04b 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d043 b101319Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd04e (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10d04e 0x48 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d043 b101319Bytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd051 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10d051 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d043 b101319Bytes 14 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd059 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b101319Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b101319Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b101319Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b101319Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Blocks
