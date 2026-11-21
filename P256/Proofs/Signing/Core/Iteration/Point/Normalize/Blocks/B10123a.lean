import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b10123aBytes : List UInt8 :=
  [76, 137, 239, 72, 141, 156, 36, 240, 0, 0, 0, 72, 137, 222]

def b10123aEffect (s : RamState) : Effect :=
  { rip := 0x10cf7d
    writes := [⟨(.reg 7 : Operand 64),(Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.reg 3 : Operand 64),stackPtr s+240⟩,
      ⟨(.reg 6 : Operand 64),stackPtr s+240⟩] }

theorem b10123a_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10cf6f)
      (codeRange 0x10cf6f b10123aBytes) (Effect.post b10123aEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10cf6f 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xcf72 (by decide))
  advance_then (lea_r64_effect_step 0x10cf72 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 240)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cf6f b10123aBytes 3 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcf7a (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10cf7a 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cf6f b10123aBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcf7d (by decide))⟩
  advance_finish [b10123aEffect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB]

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Blocks
