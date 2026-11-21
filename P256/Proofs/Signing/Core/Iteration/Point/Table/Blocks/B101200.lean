import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b101200Bytes : List UInt8 :=
  [76, 137, 239, 72, 137, 222]

def b101200Effect (s : RamState) : Effect :=
  { rip := 0x10cf3b
    writes := [⟨(.reg 7 : Operand 64),(Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 3 : Operand 64).read s⟩] }

theorem b101200_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10cf35)
      (codeRange 0x10cf35 b101200Bytes) (Effect.post b101200Effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10cf35 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xcf38 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10cf38 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cf35 b101200Bytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xcf3b (by decide))⟩
  advance_finish [b101200Effect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB]

end P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
