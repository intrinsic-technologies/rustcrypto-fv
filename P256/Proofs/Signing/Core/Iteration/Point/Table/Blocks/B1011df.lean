import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b1011dfBytes : List UInt8 :=
  [0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xfe]

def b1011dfEffect (s : RamState) : Effect :=
  { rip := 0x10cf1f
    writes := [⟨(.reg 1 : Operand 64),12⟩,
      ⟨(.reg 7 : Operand 64),(Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩] }

theorem b1011df_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10cf14)
      (codeRange 0x10cf14 b1011dfBytes) (Effect.post b1011dfEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10cf14 0xb9 (by decide) 12)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xcf19 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10cf19 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cf14 b1011dfBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcf1c (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10cf1c 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cf14 b1011dfBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcf1f (by decide))⟩
  advance_finish [b1011dfEffect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB]

end P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
