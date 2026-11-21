import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

def b10114aBytes : List UInt8 :=
  [0x4c, 0x89, 0xff, 0x48, 0x89, 0xc6]

def b10114aEffect (s : RamState) : Effect :=
  { rip := 0x10ce8d
    writes := [⟨(.reg 7 : Operand 64),(Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 0 : Operand 64).read s⟩] }

theorem b10114a_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10ce87)
      (codeRange 0x10ce87 b10114aBytes) (Effect.post b10114aEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10ce87 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xce8a (by decide))
  advance_then (mov_r64_r64_effect_step 0x10ce8a 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ce87 b10114aBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xce8d (by decide))⟩
  advance_finish [b10114aEffect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB]

end P256.Proofs.Signing.Core.Iteration.Point.Table.Blocks
