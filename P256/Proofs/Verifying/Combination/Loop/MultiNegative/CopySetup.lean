import P256.Proofs.Verifying.Combination.Loop.MultiNegative.State
import P256.Proofs.Verifying.Combination.Loop.MultiRegisterSetup
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Negative

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def copySetupBytes : List UInt8 :=
  [0x48,0x8d,0x34,0x28,0xb9,0xc,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0xa8,0x0,0x0,0x0]

def copySetupEffect (s : RamState) : Effect :=
  { rip := 0x10f201
    writes := [⟨(.reg 6 : Operand 64), s.regValue .rax + s.regValue .rbp⟩,
      ⟨(.reg 1 : Operand 64), 12⟩, ⟨(.reg 7 : Operand 64), stackPtr s + 168⟩] }

set_option maxRecDepth 4096 in
theorem copySetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f1f0)
      (codeRange 0x10f1f0 copySetupBytes) (Effect.post copySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10f1f0 0x48 (by simp [RexWPrefix]) 6 (.sib 0 (some 5) 0 .none) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf1f4 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10f1f4 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10f1f0 copySetupBytes 4 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf1f9 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10f1f9 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f1f0 copySetupBytes 9 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf201 (by decide))⟩
  advance_finish [copySetupEffect, BitVec.shiftLeft_zero, BitVec.add_zero]

end P256.Proofs.Verifying.Combination.Loop.Multi.Negative
