import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b100fa3Bytes : List UInt8 :=
  [0xb9, 0xc, 0x0, 0x0, 0x0, 0x48, 0x89, 0xef, 0x48, 0xc7, 0xc6, 0xc8, 0x2a, 0x20, 0x0]

def b100fa3Effect (s : RamState) : Effect :=
  { rip := 0x10cd6a
    writes := [⟨(.reg 1 : Operand 64),12⟩,
      ⟨(.reg 7 : Operand 64),(Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),2108104⟩] }

theorem b100fa3_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10cd5b)
      (codeRange 0x10cd5b b100fa3Bytes) (Effect.post b100fa3Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10cd5b 0xb9 (by decide) 12)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xcd60 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10cd60 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cd5b b100fa3Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcd63 (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x10cd63 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x202ac8)
  case sub => exact codeRange_slice_subset 0x10cd5b b100fa3Bytes 8 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcd6a (by decide))⟩
  advance_finish [b100fa3Effect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB]

end P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
