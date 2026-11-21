import P256.Proofs.Verifying.Wrapper.KeyArguments

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def messageArgumentBytes : List UInt8 :=
  [72, 141, 124, 36, 72, 72, 141, 180, 36, 168, 0, 0, 0, 72, 141, 148, 36, 152, 0, 0, 0, 73, 137, 224, 185, 1, 0, 0, 0]

def messageArgumentEffect (s : RamState) : Effect :=
  { rip := 0x1031e4
    writes := [⟨(.reg 7 : Operand 64),(Operand.reg 4 : Operand 64).read s+72⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 4 : Operand 64).read s+168⟩,
      ⟨(.reg 2 : Operand 64),(Operand.reg 4 : Operand 64).read s+152⟩,
      ⟨(.reg 8 : Operand 64),(Operand.reg 4 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64),1⟩] }

theorem message_arguments [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1031c7)
      (codeRange 0x1031c7 messageArgumentBytes) (Effect.post messageArgumentEffect) := by
  advance_begin (lea_r64_effect_step 0x1031c7 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x31cc (by decide))
  advance_then (lea_r64_effect_step 0x1031cc 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1031c7 messageArgumentBytes 5 8
  case mid =>
    intro s t h hh ho
    exact ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x31d4 (by decide))⟩
  advance_then (lea_r64_effect_step 0x1031d4 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1031c7 messageArgumentBytes 13 8
  case mid =>
    intro s t h hh ho
    exact ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x31dc (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1031dc 0x49 0xe0 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1031c7 messageArgumentBytes 21 3
  case mid =>
    intro s t h hh ho
    exact ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x31df (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x1031df 0xb9 (by decide) 1)
  case sub => exact codeRange_slice_subset 0x1031c7 messageArgumentBytes 24 5
  case mid =>
    intro s t h hh ho
    exact ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x31e4 (by decide))⟩
  advance_finish [messageArgumentEffect]

end P256.Proofs.Verifying.Wrapper
