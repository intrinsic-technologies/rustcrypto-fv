import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Instructions.MovzxByte

def yConversionArgumentsBytes : List UInt8 :=
  [0x48,0x8d,0x7c,0x24,0x10,0x48,0x8d,0x84,0x24,0xa8,0x0,0x0,0x0,0x41,0xb8,0x1,0x0,0x0,0x0,0x48,0x89,0xf5,0x48,0x89,0xc6,0x48,0xc7,0xc2,0xc8,0x2d,0x20,0x0,0x48,0xc7,0xc1,0x88,0x2d,0x20,0x0]

def yConversionArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x11072b
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 16⟩,
      ⟨(.reg 0 : Operand 64), stackPtr s + 168⟩,
      ⟨(.reg 8 : Operand 64), 1⟩,
      ⟨(.reg 5 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 168⟩,
      ⟨(.reg 2 : Operand 64), 0x202dc8⟩,
      ⟨(.reg 1 : Operand 64), 0x202d88⟩] }

set_option maxHeartbeats 800000 in
theorem y_conversion_arguments_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110704)
      (codeRange 0x110704 yConversionArgumentsBytes) yConversionArgumentsEffect := by
  have width (x : BitVec 8) : ((x.setWidth 64).setWidth 32).setWidth 64 = x.setWidth 64 := by
    rw [BitVec.setWidth_setWidth_of_le x (show 32 ≤ 64 by decide),
      BitVec.setWidth_setWidth (by decide)]
  unfold yConversionArgumentsBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x110704 7 (.sib 4 none 0 (.d8 16))) from
    lea_r64_effect_step 0x110704 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 16))
      (by constructor <;> decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10709 (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x110709 0 (.sib 4 none 0 (.d32 168))) from
    lea_r64_effect_step 0x110709 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 168))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110704) 5 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10711 (by decide))
  slice_run_then (show StepEffect _ _ (movR32Imm32Effect 0x110711 6 8 1) from
    mov_r32_imm32_rex_effect_step 0x110711 0x41 0xb8 (by simp [RexNoWPrefix]) (by decide) 1)
  case sub => exact codeRange_mem_of_drop (p := 0x110704) 13 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10717 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110717 5 6) from
    mov_r64_r64_effect_step 0x110717 0x48 0xf5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110704) 19 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1071a (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x11071a 6 0) from
    mov_r64_r64_effect_step 0x11071a 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110704) 22 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1071d (by decide))
  slice_run_then (show StepEffect _ _ (movR64Imm32Effect 0x11071d 2 0x202dc8) from
    mov_r64_imm32_effect_step 0x11071d 0x48 0xc2 (by simp [RexWPrefix]) rfl rfl 0x202dc8)
  case sub => exact codeRange_mem_of_drop (p := 0x110704) 25 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10724 (by decide))
  slice_run_then (show StepEffect _ _ (movR64Imm32Effect 0x110724 1 0x202d88) from
    mov_r64_imm32_effect_step 0x110724 0x48 0xc1 (by simp [RexWPrefix]) rfl rfl 0x202d88)
  case sub => exact codeRange_mem_of_drop (p := 0x110704) 32 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1072b (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [yConversionArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · x86_norm [yConversionArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · intro f; cases f <;> x86_norm [yConversionArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · x86_norm [yConversionArgumentsEffect, width]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks
