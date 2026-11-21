import P256.Proofs.Verifying.Wrapper.KeyArguments

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def affineArgumentBytes : List UInt8 :=
  [72, 141, 116, 36, 80, 72, 141, 188, 36, 168, 0, 0, 0, 185, 9, 0, 0, 0]

def affineArgumentEffect (s : RamState) : Effect :=
  { rip := 0x103115
    writes := [⟨(.reg 6 : Operand 64),(Operand.reg 4 : Operand 64).read s+80⟩,
      ⟨(.reg 7 : Operand 64),(Operand.reg 4 : Operand 64).read s+168⟩,
      ⟨(.reg 1 : Operand 64),9⟩] }

theorem affine_arguments [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x103103)
      (codeRange 0x103103 affineArgumentBytes) (Effect.post affineArgumentEffect) := by
  advance_begin (lea_r64_effect_step 0x103103 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x3108 (by decide))
  advance_then (lea_r64_effect_step 0x103108 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103103 affineArgumentBytes 5 8
  case mid =>
    intro s t h hh ho
    exact ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x3110 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x103110 0xb9 (by decide) 9)
  case sub => exact codeRange_slice_subset 0x103103 affineArgumentBytes 13 5
  case mid =>
    intro s t h hh ho
    exact ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x3115 (by decide))⟩
  advance_finish [affineArgumentEffect]

end P256.Proofs.Verifying.Wrapper
