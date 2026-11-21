import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b101379Bytes : List UInt8 :=
  [185, 9, 0, 0, 0, 72, 137, 239, 76, 137, 254]

def b101379Effect (s : RamState) : Effect :=
  { rip := 0x10d0a8
    writes := [⟨(.reg 1 : Operand 64),9⟩,
      ⟨(.reg 7 : Operand 64),(Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩] }

theorem b101379_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d09d)
      (codeRange 0x10d09d b101379Bytes) (Effect.post b101379Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10d09d 0xb9 (by decide) 9)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd0a2 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10d0a2 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d09d b101379Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd0a5 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10d0a5 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d09d b101379Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd0a8 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b101379Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b101379Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b101379Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b101379Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks
