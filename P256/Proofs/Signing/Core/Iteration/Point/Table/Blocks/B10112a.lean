import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b10112aBytes : List UInt8 :=
  [0xb9, 0xc, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x84, 0x24, 0x90, 0x3, 0x0, 0x0, 0x48, 0x89, 0xc7, 0x4c, 0x89, 0xee]

def b10112aEffect (s : RamState) : Effect :=
  { rip := 0x10ce72
    writes := [⟨(.reg 1 : Operand 64),12⟩,
      ⟨(.reg 0 : Operand 64),stackPtr s+912⟩,
      ⟨(.reg 7 : Operand 64),stackPtr s+912⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 13 : Operand 64).read s⟩] }

theorem b10112a_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10ce5f)
      (codeRange 0x10ce5f b10112aBytes) (Effect.post b10112aEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10ce5f 0xb9 (by decide) 12)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xce64 (by decide))
  advance_then (lea_r64_effect_step 0x10ce64 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 912)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ce5f b10112aBytes 5 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xce6c (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10ce6c 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ce5f b10112aBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xce6f (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10ce6f 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ce5f b10112aBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xce72 (by decide))⟩
  advance_finish [b10112aEffect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB]

end P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
