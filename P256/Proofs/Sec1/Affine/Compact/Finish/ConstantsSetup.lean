import P256.Proofs.Sec1.Affine.State
import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice

def constantsSetupBytes : List UInt8 :=
  [0x48,0x8d,0x84,0x24,0xa8,0x0,0x0,0x0,0xb9,0x9,0x0,0x0,0x0,0x48,0x89,0xc7,0x48,0xc7,0xc6,0xf8,0x2d,0x20,0x0]

def constantsSetupEffect (s : RamState) : Effect :=
  { rip := 0x11057c
    writes := [⟨(.reg 0 : Operand 64), stackPtr s + 168⟩,
      ⟨(.reg 1 : Operand 64), 9⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 168⟩,
      ⟨(.reg 6 : Operand 64), 0x202df8⟩] }

theorem constants_setup [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110565)
      (codeRange 0x110565 constantsSetupBytes) constantsSetupEffect := by
  unfold constantsSetupBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x110565 0 (.sib 4 none 0 (.d32 168))) from
    lea_r64_effect_step 0x110565 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 168))
      (by constructor <;> decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1056d (by decide))
  slice_run_then (show StepEffect _ _ (movR32Imm32Effect 0x11056d 5 1 9) from
    mov_r32_imm32_effect_step 0x11056d 0xb9 (by decide) 9)
  case sub => exact codeRange_mem_of_drop (p := 0x110565) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10572 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110572 7 0) from
    mov_r64_r64_effect_step 0x110572 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110565) 13 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10575 (by decide))
  slice_run_then (show StepEffect _ _ (movR64Imm32Effect 0x110575 6 0x202df8) from
    mov_r64_imm32_effect_step 0x110575 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x202df8)
  case sub => exact codeRange_mem_of_drop (p := 0x110565) 16 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1057c (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [constantsSetupEffect]
  · x86_norm [constantsSetupEffect]
  · intro f; cases f <;> x86_norm [constantsSetupEffect]
  · x86_norm [constantsSetupEffect]

end P256.Proofs.Sec1.Affine.Compact.Finish
