import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b1010b8Bytes : List UInt8 :=
  [0xb9, 0xc, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x84, 0x24, 0xd0, 0x2, 0x0, 0x0, 0x48, 0x89, 0xc7, 0x4c, 0x89, 0xee]

def b1010b8Effect (s : RamState) : Effect :=
  { rip := 0x10cdf0
    writes := [⟨(.reg 1 : Operand 64),12⟩,
      ⟨(.reg 0 : Operand 64),stackPtr s+720⟩,
      ⟨(.reg 7 : Operand 64),stackPtr s+720⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 13 : Operand 64).read s⟩] }

theorem b1010b8_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10cddd)
      (codeRange 0x10cddd b1010b8Bytes) (Effect.post b1010b8Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10cddd 0xb9 (by decide) 12)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xcde2 (by decide))
  advance_then (lea_r64_effect_step 0x10cde2 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 720)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cddd b1010b8Bytes 5 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcdea (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10cdea 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cddd b1010b8Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcded (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10cded 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cddd b1010b8Bytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcdf0 (by decide))⟩
  advance_finish [b1010b8Effect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB]

end P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
