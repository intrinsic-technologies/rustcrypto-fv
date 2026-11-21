import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Pad

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field

def copySetupBytes : List UInt8 := [0x48,0x8d,0xbc,0x24,0xa8,0,0,0,0x4c,0x89,0xe6,0x48,0x89,0xea]

def copySetupEffect (s : RamState) : Effect :=
  { rip := 0x106a37
    writes := [⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 168⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩] }

theorem copy_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x106a29)
      (codeRange 0x106a29 copySetupBytes) (Effect.post copySetupEffect) := by
  have h1 := boundary_ne_program outside (inProgram_of_textOffset 0x6a31 (by decide))
  have h2 := boundary_ne_program outside (inProgram_of_textOffset 0x6a34 (by decide))
  have h3 := boundary_ne_program outside (inProgram_of_textOffset 0x6a37 (by decide))
  advance_begin lea_r64_effect_step 0x106a29 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl
  advance_then mov_r64_r64_effect_step 0x106a31 0x4c 0xe6 (by simp [RexWPrefix]) rfl
  case sub => exact codeRange_slice_subset 0x106a29 copySetupBytes 8 3
  advance_then mov_r64_r64_effect_step 0x106a34 0x48 0xea (by simp [RexWPrefix]) rfl
  case sub => exact codeRange_slice_subset 0x106a29 copySetupBytes 11 3
  advance_finish [copySetupEffect, gprNumber, rexB, rexR, modrmRm, modrmReg,
    UInt8.toBitVec_ofNat]

end P256.Proofs.EcdhWrapper.Peer.Pad
