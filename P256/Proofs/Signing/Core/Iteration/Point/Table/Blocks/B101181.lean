import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b101181Bytes : List UInt8 :=
  [0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xff, 0x48, 0xc7, 0xc6, 0xc8, 0x2a, 0x20, 0x0]

def b101181Effect (s : RamState) : Effect :=
  { rip := 0x10cec5
    writes := [⟨(.reg 1 : Operand 64),12⟩,
      ⟨(.reg 7 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),2108104⟩] }

theorem b101181_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10ceb6)
      (codeRange 0x10ceb6 b101181Bytes) (Effect.post b101181Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10ceb6 0xb9 (by decide) 12)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xcebb (by decide))
  advance_then (mov_r64_r64_effect_step 0x10cebb 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ceb6 b101181Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcebe (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x10cebe 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x202ac8)
  case sub => exact codeRange_slice_subset 0x10ceb6 b101181Bytes 8 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcec5 (by decide))⟩
  advance_finish [b101181Effect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB]

end P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
