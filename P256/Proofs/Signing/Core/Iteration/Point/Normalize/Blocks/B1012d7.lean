import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b1012d7Bytes : List UInt8 :=
  [76, 137, 255, 76, 141, 116, 36, 8, 76, 137, 246, 72, 137, 234]

def b1012d7Effect (s : RamState) : Effect :=
  { rip := 0x10d01a
    writes := [⟨(.reg 7 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 14 : Operand 64),stackPtr s+8⟩,
      ⟨(.reg 6 : Operand 64),stackPtr s+8⟩,
      ⟨(.reg 2 : Operand 64),(Operand.reg 5 : Operand 64).read s⟩] }

theorem b1012d7_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d00c)
      (codeRange 0x10d00c b1012d7Bytes) (Effect.post b1012d7Effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10d00c 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd00f (by decide))
  advance_then (lea_r64_effect_step 0x10d00f 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d00c b1012d7Bytes 3 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd014 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10d014 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d00c b1012d7Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd017 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10d017 0x48 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d00c b1012d7Bytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd01a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [b1012d7Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b1012d7Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [b1012d7Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [b1012d7Effect,stackPtr,BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Blocks
