import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b10111cBytes : List UInt8 :=
  [0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xfe]

def b10111cEffect (s : RamState) : Effect :=
  { rip := 0x10ce5c
    writes := [⟨(.reg 1 : Operand 64),12⟩,
      ⟨(.reg 7 : Operand 64),(Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩] }

theorem b10111c_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10ce51)
      (codeRange 0x10ce51 b10111cBytes) (Effect.post b10111cEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10ce51 0xb9 (by decide) 12)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xce56 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10ce56 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ce51 b10111cBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xce59 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10ce59 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ce51 b10111cBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xce5c (by decide))⟩
  advance_finish [b10111cEffect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB]

end P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
