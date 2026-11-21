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

def xFieldArgumentsBytes : List UInt8 :=
  [0x4c, 0x8d, 0xac, 0x24, 0xe0, 0x1, 0x0, 0x0, 0x48, 0x8d, 0xb4, 0x24, 0xf8, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x94, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x44, 0x89, 0xf9]

def xFieldArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x1109f5
    writes := [⟨(.reg 13 : Operand 64), stackPtr s + 480⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 248⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 168⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 480⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.reg 15 : Operand 64).read s).setWidth 32 |>.setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem x_field_arguments_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x1109d7)
      (codeRange 0x1109d7 xFieldArgumentsBytes) xFieldArgumentsEffect := by
  have width (x : BitVec 8) : ((x.setWidth 64).setWidth 32).setWidth 64 = x.setWidth 64 := by
    rw [BitVec.setWidth_setWidth_of_le x (show 32 ≤ 64 by decide),
      BitVec.setWidth_setWidth (by decide)]
  unfold xFieldArgumentsBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x1109d7 13 (.sib 4 none 0 (.d32 480))) from
    lea_r64_effect_step 0x1109d7 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 480))
      (by constructor <;> decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x109df (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x1109df 6 (.sib 4 none 0 (.d32 248))) from
    lea_r64_effect_step 0x1109df 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 248))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1109d7) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x109e7 (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x1109e7 2 (.sib 4 none 0 (.d32 168))) from
    lea_r64_effect_step 0x1109e7 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 168))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1109d7) 16 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x109ef (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x1109ef 7 13) from
    mov_r64_r64_effect_step 0x1109ef 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1109d7) 24 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x109f2 (by decide))
  slice_run_then (show StepEffect _ _ (movR32R32Effect 0x1109f2 3 1 15) from
    mov_r32_r32_rex_effect_step 0x1109f2 0x44 0xf9 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1109d7) 27 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x109f5 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [xFieldArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · x86_norm [xFieldArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · intro f; cases f <;> x86_norm [xFieldArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · x86_norm [xFieldArgumentsEffect, width]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks
