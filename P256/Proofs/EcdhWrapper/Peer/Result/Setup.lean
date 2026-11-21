import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Result

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field

def setupBytes : List UInt8 :=
  [0x48,0x8d,0x94,0x24,0xa8,0,0,0,0x48,0x8d,0xb4,0x24,0x78,1,0,0,
   0xb9,9,0,0,0,0x48,0x89,0xd7]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x106bc2
    writes := [⟨(.reg 2 : Operand 64),(Operand.reg 4 : Operand 64).read s+168⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 4 : Operand 64).read s+376⟩,
      ⟨(.reg 1 : Operand 64),9⟩,
      ⟨(.reg 7 : Operand 64),(Operand.reg 4 : Operand 64).read s+168⟩] }

theorem setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP=0x106baa)
      (codeRange 0x106baa setupBytes) (Effect.post setupEffect) := by
  have h1 := boundary_ne_program outside (inProgram_of_textOffset 0x6bb2 (by decide))
  have h2 := boundary_ne_program outside (inProgram_of_textOffset 0x6bba (by decide))
  have h3 := boundary_ne_program outside (inProgram_of_textOffset 0x6bbf (by decide))
  have h4 := boundary_ne_program outside (inProgram_of_textOffset 0x6bc2 (by decide))
  advance_begin lea_r64_effect_step 0x106baa 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl
  advance_then lea_r64_effect_step 0x106bb2 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 376)) (by decide) rfl rfl
  case sub => exact codeRange_slice_subset 0x106baa setupBytes 8 8
  advance_then mov_r32_imm32_effect_step 0x106bba 0xb9 (by decide) 9
  case sub => exact codeRange_slice_subset 0x106baa setupBytes 16 5
  advance_then mov_r64_r64_effect_step 0x106bbf 0x48 0xd7 (by simp [RexWPrefix]) rfl
  case sub => exact codeRange_slice_subset 0x106baa setupBytes 21 3
  advance_finish [setupEffect,gprNumber,rexB,rexR,modrmRm,modrmReg,UInt8.toBitVec_ofNat]

end P256.Proofs.EcdhWrapper.Peer.Result
