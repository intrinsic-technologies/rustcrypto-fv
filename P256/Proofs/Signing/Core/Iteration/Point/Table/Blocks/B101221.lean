import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b101221Bytes : List UInt8 :=
  [186, 1, 0, 0, 0, 65, 184, 1, 0, 0, 0, 72, 141, 188, 36, 176, 0, 0, 0, 76, 137, 254, 76, 137, 233]

def b101221Effect (s : RamState) : Effect :=
  { rip := 0x10cf6a
    writes := [⟨(.reg 2 : Operand 64),1⟩,
      ⟨(.reg 8 : Operand 64),1⟩,
      ⟨(.reg 7 : Operand 64),stackPtr s+176⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64),(Operand.reg 13 : Operand 64).read s⟩] }

theorem b101221_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10cf51)
      (codeRange 0x10cf51 b101221Bytes) (Effect.post b101221Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10cf51 0xba (by decide) 1)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xcf56 (by decide))
  advance_then (mov_r32_imm32_rex_effect_step 0x10cf56 0x41 0xb8 (by simp [RexNoWPrefix]) (by decide) 1)
  case sub => exact codeRange_slice_subset 0x10cf51 b101221Bytes 5 6
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcf5c (by decide))⟩
  advance_then (lea_r64_effect_step 0x10cf5c 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cf51 b101221Bytes 11 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcf64 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10cf64 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cf51 b101221Bytes 19 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcf67 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10cf67 0x4c 0xe9 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cf51 b101221Bytes 22 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcf6a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b101221Effect,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b101221Effect,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b101221Effect,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b101221Effect,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
