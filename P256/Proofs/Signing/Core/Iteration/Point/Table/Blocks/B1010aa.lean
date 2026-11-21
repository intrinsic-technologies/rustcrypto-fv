import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b1010aaBytes : List UInt8 :=
  [0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xfe]

def b1010aaEffect (s : RamState) : Effect :=
  { rip := 0x10cdda
    writes := [⟨(.reg 1 : Operand 64),12⟩,
      ⟨(.reg 7 : Operand 64),(Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩] }

theorem b1010aa_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10cdcf)
      (codeRange 0x10cdcf b1010aaBytes) (Effect.post b1010aaEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10cdcf 0xb9 (by decide) 12)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xcdd4 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10cdd4 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cdcf b1010aaBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcdd7 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10cdd7 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cdcf b1010aaBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcdda (by decide))⟩
  advance_finish [b1010aaEffect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB]

end P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
