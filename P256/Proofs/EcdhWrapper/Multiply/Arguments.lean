import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Multiply

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field

def argumentBytes : List UInt8 :=
  [0x48,0x89,0xe7,0x48,0x8d,0xb4,0x24,0x58,1,0,0]

def argumentEffect (s : RamState) : Effect :=
  { rip := 0x106bd0
    writes := [⟨(.reg 7 : Operand 64),(Operand.reg 4 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 4 : Operand 64).read s+344⟩] }

theorem arguments [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP=0x106bc5)
      (codeRange 0x106bc5 argumentBytes) (Effect.post argumentEffect) := by
  have h1 := boundary_ne_program outside (inProgram_of_textOffset 0x6bc8 (by decide))
  have h2 := boundary_ne_program outside (inProgram_of_textOffset 0x6bd0 (by decide))
  advance_begin mov_r64_r64_effect_step 0x106bc5 0x48 0xe7 (by simp [RexWPrefix]) rfl
  advance_then lea_r64_effect_step 0x106bc8 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 344)) (by decide) rfl rfl
  case sub => exact codeRange_slice_subset 0x106bc5 argumentBytes 3 8
  advance_finish [argumentEffect,gprNumber,rexB,rexR,modrmRm,modrmReg,UInt8.toBitVec_ofNat]

end P256.Proofs.EcdhWrapper.Multiply
