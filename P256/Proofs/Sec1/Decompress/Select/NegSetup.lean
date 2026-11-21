import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Select

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def negSetupBytes : List UInt8 :=
  [0x4c,0x8d,0xac,0x24,0x28,1,0,0,0x48,0x89,0xe6,0x4c,0x89,0xef]

def negSetupEffect (s : RamState) : Effect :=
  { rip := 0x10ff72
    writes := [⟨(.reg 13 : Operand 64), stackPtr s + 296⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 296⟩] }

theorem neg_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10ff64) (codeRange 0x10ff64 negSetupBytes)
      (Effect.post negSetupEffect) := by
  have h1 := boundary_ne_program hout (inProgram_of_textOffset 0xff6c (by decide +kernel))
  have h2 := boundary_ne_program hout (inProgram_of_textOffset 0xff6f (by decide +kernel))
  have h3 := boundary_ne_program hout (inProgram_of_textOffset 0xff72 (by decide +kernel))
  advance_begin (lea_r64_effect_step 0x10ff64 0x4c (by simp [RexWPrefix])
    5 (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  advance_then (mov_r64_r64_effect_step 0x10ff6c 0x48 0xe6 (by simp [RexWPrefix]) rfl)
  advance_then (mov_r64_r64_effect_step 0x10ff6f 0x4c 0xef (by simp [RexWPrefix]) rfl)
  advance_finish [negSetupEffect, stackPtr, Operand.read_reg64,
    gprNumber, rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec]
  all_goals first
    | exact codeRange_slice_subset 0x10ff64 negSetupBytes 8 3
    | exact codeRange_slice_subset 0x10ff64 negSetupBytes 11 3
    | (repeat constructor <;> rfl)

theorem negSetupBytes_extracted : Extracted.textBytes.toListFrom 0xff64 14 = negSetupBytes := by decide +kernel

end P256.Proofs.Sec1.Decompress.Select
