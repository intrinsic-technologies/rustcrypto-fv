import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b101210Bytes : List UInt8 :=
  [186, 0, 3, 0, 0, 76, 137, 255, 72, 137, 238]

def b101210Effect (s : RamState) : Effect :=
  { rip := 0x10cf4b
    writes := [⟨(.reg 2 : Operand 64),768⟩,
      ⟨(.reg 7 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 5 : Operand 64).read s⟩] }

theorem b101210_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10cf40)
      (codeRange 0x10cf40 b101210Bytes) (Effect.post b101210Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10cf40 0xba (by decide) 768)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xcf45 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10cf45 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cf40 b101210Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcf48 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10cf48 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cf40 b101210Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcf4b (by decide))⟩
  advance_finish [b101210Effect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB]

end P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
