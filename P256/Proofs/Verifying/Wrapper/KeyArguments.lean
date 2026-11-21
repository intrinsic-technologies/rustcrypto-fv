import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def keyArgumentBytes : List UInt8 :=
  [72, 141, 124, 36, 72, 72, 137, 230, 186, 65, 0, 0, 0]

def keyArgumentEffect (s : RamState) : Effect :=
  { rip := 0x1030f3
    writes := [⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s+72⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), 65⟩] }

theorem key_arguments [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1030e6)
      (codeRange 0x1030e6 keyArgumentBytes) (Effect.post keyArgumentEffect) := by
  advance_begin (lea_r64_effect_step 0x1030e6 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x30eb (by decide))
  advance_then (mov_r64_r64_effect_step 0x1030eb 0x48 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1030e6 keyArgumentBytes 5 3
  case mid =>
    intro s t h hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x30ee (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x1030ee 0xba (by decide) 65)
  case sub => exact codeRange_slice_subset 0x1030e6 keyArgumentBytes 8 5
  case mid =>
    intro s t h hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x30f3 (by decide))⟩
  advance_finish [keyArgumentEffect]

end P256.Proofs.Verifying.Wrapper
