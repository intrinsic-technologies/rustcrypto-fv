import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Select

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def selectSetupBytes : List UInt8 :=
  [0x44,0x8b,0x7c,0x24,0x70,0x4c,0x8d,0xa4,0x24,0x98,0,0,0,
    0x48,0x8d,0xb4,0x24,0xc0,0,0,0,0x4c,0x89,0xe7,0x4c,0x89,0xea,0x44,0x89,0xf9]

def selectSetupPre (s : RamState) : Prop :=
  LoadPre 0x10ff0e (fun s => (AddrMode.sib 4 none 0 (.d8 112)).addr s 0x10ff13) 4 s

def selectSetupEffect (s : RamState) : Effect :=
  { rip := 0x10ff2c
    writes := [⟨(.reg 15 : Operand 64), ((.mem (stackPtr s + 112) : Operand 32).read s).setWidth 64⟩,
      ⟨(.reg 12 : Operand 64), stackPtr s + 152⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 192⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 152⟩,
      ⟨(.reg 2 : Operand 64), (.reg 13 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), ((.mem (stackPtr s + 112) : Operand 32).read s).setWidth 64⟩] }

theorem select_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary selectSetupPre (codeRange 0x10ff0e selectSetupBytes)
      (Effect.post selectSetupEffect) := by
  have h1 := boundary_ne_program hout (inProgram_of_textOffset 0xff13 (by decide +kernel))
  have h2 := boundary_ne_program hout (inProgram_of_textOffset 0xff1b (by decide +kernel))
  have h3 := boundary_ne_program hout (inProgram_of_textOffset 0xff23 (by decide +kernel))
  have h4 := boundary_ne_program hout (inProgram_of_textOffset 0xff26 (by decide +kernel))
  have h5 := boundary_ne_program hout (inProgram_of_textOffset 0xff29 (by decide +kernel))
  have h6 := boundary_ne_program hout (inProgram_of_textOffset 0xff2c (by decide +kernel))
  have step1 : StepEffect selectSetupPre (codeRange 0x10ff0e [0x44,0x8b,0x7c,0x24,0x70])
      (movR32M32Effect 0x10ff0e 15 (.sib 4 none 0 (.d8 112))) :=
    mov_r32_m32_effect_step 0x10ff0e 0x44 (by simp [RexNoWPrefix]) 7
      (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl
  advance_begin step1
  advance_then (lea_r64_effect_step 0x10ff13 0x4c (by simp [RexWPrefix])
    4 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  advance_then (lea_r64_effect_step 0x10ff1b 0x48 (by simp [RexWPrefix])
    6 (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  advance_then (mov_r64_r64_effect_step 0x10ff23 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  advance_then (mov_r64_r64_effect_step 0x10ff26 0x4c 0xea (by simp [RexWPrefix]) rfl)
  advance_then (mov_r32_r32_rex_effect_step 0x10ff29 0x44 0xf9 (by simp [RexNoWPrefix]) rfl)
  advance_finish [selectSetupEffect, selectSetupPre, stackPtr, Operand.read_reg64,
    gprNumber, rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
  all_goals first
    | exact codeRange_slice_subset 0x10ff0e selectSetupBytes 5 8
    | exact codeRange_slice_subset 0x10ff0e selectSetupBytes 13 8
    | exact codeRange_slice_subset 0x10ff0e selectSetupBytes 21 3
    | exact codeRange_slice_subset 0x10ff0e selectSetupBytes 24 3
    | exact codeRange_slice_subset 0x10ff0e selectSetupBytes 27 3
    | (repeat constructor <;> rfl)

end P256.Proofs.Sec1.Decompress.Select
