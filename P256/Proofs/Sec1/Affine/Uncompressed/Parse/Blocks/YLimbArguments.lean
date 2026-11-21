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

def yLimbArgumentsBytes : List UInt8 :=
  [0x44, 0xf, 0xb6, 0xf0, 0x48, 0x8d, 0xbc, 0x24, 0xa8, 0x0, 0x0, 0x0, 0xbe, 0x4, 0x0, 0x0, 0x0, 0xb9, 0x4, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x54, 0x24, 0x10, 0x45, 0x89, 0xf0]

def yLimbArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x11078b
    writes := [⟨(.reg 14 : Operand 64), ((Operand.reg 0 : Operand 64).read s).setWidth 8 |>.setWidth 64⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 168⟩,
      ⟨(.reg 6 : Operand 64), 4⟩,
      ⟨(.reg 1 : Operand 64), 4⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 16⟩,
      ⟨(.reg 8 : Operand 64), ((Operand.reg 0 : Operand 64).read s).setWidth 8 |>.setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem y_limb_arguments_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x11076d)
      (codeRange 0x11076d yLimbArgumentsBytes) yLimbArgumentsEffect := by
  have width (x : BitVec 8) : ((x.setWidth 64).setWidth 32).setWidth 64 = x.setWidth 64 := by
    rw [BitVec.setWidth_setWidth_of_le x (show 32 ≤ 64 by decide),
      BitVec.setWidth_setWidth (by decide)]
  unfold yLimbArgumentsBytes
  slice_run_begin (show StepEffect _ _ (movzxR32R8Effect 0x11076d 4 14 0) from
    movzx_r32_r8_rex_effect_step 0x11076d 0x44 0xf0 (by simp [RexNoWPrefix]) rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10771 (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x110771 7 (.sib 4 none 0 (.d32 168))) from
    lea_r64_effect_step 0x110771 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 168))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11076d) 4 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10779 (by decide))
  slice_run_then (show StepEffect _ _ (movR32Imm32Effect 0x110779 5 6 4) from
    mov_r32_imm32_effect_step 0x110779 0xbe (by decide) 4)
  case sub => exact codeRange_mem_of_drop (p := 0x11076d) 12 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1077e (by decide))
  slice_run_then (show StepEffect _ _ (movR32Imm32Effect 0x11077e 5 1 4) from
    mov_r32_imm32_effect_step 0x11077e 0xb9 (by decide) 4)
  case sub => exact codeRange_mem_of_drop (p := 0x11076d) 17 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10783 (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x110783 2 (.sib 4 none 0 (.d8 16))) from
    lea_r64_effect_step 0x110783 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11076d) 22 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10788 (by decide))
  slice_run_then (show StepEffect _ _ (movR32R32Effect 0x110788 3 8 14) from
    mov_r32_r32_rex_effect_step 0x110788 0x45 0xf0 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11076d) 27 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1078b (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [yLimbArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · x86_norm [yLimbArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · intro f; cases f <;> x86_norm [yLimbArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · x86_norm [yLimbArgumentsEffect, width]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks
