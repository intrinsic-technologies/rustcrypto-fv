import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Copy

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field

def setupBytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0x80,0x0,0x0,0x0,0x48,0x8d,0xb4,0x24,0xd8,0x1,0x0,0x0,0xb9,0xd,0x0,0x0,0x0]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10d732
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 128⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 472⟩,
      ⟨(.reg 1 : Operand 64), 13⟩] }

theorem setup_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d71d)
      (codeRange 0x10d71d setupBytes) (Effect.post setupEffect) := by
  advance_begin (lea_r64_effect_step 0x10d71d 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case next => exact fun _ _ =>
    boundary_ne_program outside (inProgram_of_textOffset 0xd725 (by decide))
  advance_then (lea_r64_effect_step 0x10d725 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 472)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d71d setupBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd72d (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10d72d 0xb9 (by decide) 13)
  case sub => exact codeRange_slice_subset 0x10d71d setupBytes 16 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd732 (by decide))⟩
  advance_finish [setupEffect]

end P256.Proofs.Verifying.Message.Hash.Finalize.Copy
