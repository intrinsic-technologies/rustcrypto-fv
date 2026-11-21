import P256.Proofs.Verifying.Combination.Loop.MultiNegative.State
import P256.Proofs.Verifying.Combination.Loop.MultiRegisterSetup
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Negative

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def negateSetupBytes : List UInt8 :=
  [0x4c,0x8d,0xb4,0x24,0x28,0x1,0x0,0x0,0x4c,0x89,0xf7,0x48,0x8d,0x74,0x24,0x28]

def negateSetupEffect (s : RamState) : Effect :=
  { rip := 0x10f23c
    writes := [⟨(.reg 14 : Operand 64), stackPtr s + 296⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 296⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 40⟩] }

set_option maxRecDepth 4096 in
theorem negateSetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f22c)
      (codeRange 0x10f22c negateSetupBytes) (Effect.post negateSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10f22c 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf234 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10f234 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f22c negateSetupBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf237 (by decide))⟩
  advance_then (lea_r64_effect_step 0x10f237 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f22c negateSetupBytes 11 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf23c (by decide))⟩
  advance_finish [negateSetupEffect, BitVec.shiftLeft_zero]

end P256.Proofs.Verifying.Combination.Loop.Multi.Negative
