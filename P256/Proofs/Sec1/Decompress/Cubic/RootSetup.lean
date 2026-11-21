import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Cubic

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def sqrtSetupBytes : List UInt8 := [0x4c,0x8d,0x6c,0x24,0x50,0x4c,0x89,0xef,0x4c,0x89,0xe6]

def sqrtSetupEffect (s : RamState) : Effect :=
  { rip := 0x10fed9
    writes := [⟨(.reg 13 : Operand 64), stackPtr s + 80⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 80⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩] }

theorem sqrt_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fece) (codeRange 0x10fece sqrtSetupBytes)
      (Effect.post sqrtSetupEffect) := by
  have h1 := boundary_ne_program hout (inProgram_of_textOffset 0xfed3 (by decide +kernel))
  have h2 := boundary_ne_program hout (inProgram_of_textOffset 0xfed6 (by decide +kernel))
  have h3 := boundary_ne_program hout (inProgram_of_textOffset 0xfed9 (by decide +kernel))
  advance_begin (lea_r64_effect_step 0x10fece 0x4c (by simp [RexWPrefix])
    5 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  advance_then (mov_r64_r64_effect_step 0x10fed3 0x4c 0xef (by simp [RexWPrefix]) rfl)
  advance_then (mov_r64_r64_effect_step 0x10fed6 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  advance_finish [sqrtSetupEffect, stackPtr, Operand.read_reg64,
    gprNumber, rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec]
  all_goals first
    | exact codeRange_slice_subset 0x10fece sqrtSetupBytes 5 3
    | exact codeRange_slice_subset 0x10fece sqrtSetupBytes 8 3
    | (repeat constructor <;> rfl)

end P256.Proofs.Sec1.Decompress.Cubic
