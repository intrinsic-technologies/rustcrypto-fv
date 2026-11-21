import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field

def copySetupBytes : List UInt8 := [0x48,0x89,0xe7,0x48,0x89,0xde,0x4c,0x89,0xf2]

def copySetupEffect (s : RamState) : Effect :=
  { rip := 0x10e55b
    writes := [⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩] }

theorem copy_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10e552)
      (codeRange 0x10e552 copySetupBytes) (Effect.post copySetupEffect) := by
  have h1 := boundary_ne_program outside (inProgram_of_textOffset 0xe555 (by decide))
  have h2 := boundary_ne_program outside (inProgram_of_textOffset 0xe558 (by decide))
  have h3 := boundary_ne_program outside (inProgram_of_textOffset 0xe55b (by decide))
  advance_begin mov_r64_r64_effect_step 0x10e552 0x48 0xe7 (by simp [RexWPrefix]) rfl
  advance_then mov_r64_r64_effect_step 0x10e555 0x48 0xde (by simp [RexWPrefix]) rfl
  case sub => exact codeRange_slice_subset 0x10e552 copySetupBytes 3 3
  advance_then mov_r64_r64_effect_step 0x10e558 0x4c 0xf2 (by simp [RexWPrefix]) rfl
  case sub => exact codeRange_slice_subset 0x10e552 copySetupBytes 6 3
  advance_finish [copySetupEffect,
    show gprNumber (0#1) (rexR (UInt8.toBitVec 72)) (modrmReg 231) = 4#5 from rfl,
    show gprNumber (0#1) (rexR (UInt8.toBitVec 72)) (modrmReg 222) = 3#5 from rfl,
    show gprNumber (0#1) (rexR (UInt8.toBitVec 76)) (modrmReg 242) = 14#5 from rfl]

end P256.Proofs.Sec1.Decode.Prepare
