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

def yFieldArgumentsBytes : List UInt8 :=
  [0x4c, 0x8d, 0xb4, 0x24, 0xc0, 0x1, 0x0, 0x0, 0x48, 0x8d, 0xb4, 0x24, 0x60, 0x2, 0x0, 0x0, 0x48, 0x8d, 0x54, 0x24, 0x60, 0x4c, 0x89, 0xf7]

def yFieldArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x11081b
    writes := [⟨(.reg 14 : Operand 64), stackPtr s + 448⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 608⟩,
      ⟨(.reg 2 : Operand 64), stackPtr s + 96⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 448⟩] }

set_option maxHeartbeats 800000 in
theorem y_field_arguments_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110803)
      (codeRange 0x110803 yFieldArgumentsBytes) yFieldArgumentsEffect := by
  have width (x : BitVec 8) : ((x.setWidth 64).setWidth 32).setWidth 64 = x.setWidth 64 := by
    rw [BitVec.setWidth_setWidth_of_le x (show 32 ≤ 64 by decide),
      BitVec.setWidth_setWidth (by decide)]
  unfold yFieldArgumentsBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x110803 14 (.sib 4 none 0 (.d32 448))) from
    lea_r64_effect_step 0x110803 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 448))
      (by constructor <;> decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1080b (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x11080b 6 (.sib 4 none 0 (.d32 608))) from
    lea_r64_effect_step 0x11080b 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 608))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110803) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10813 (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x110813 2 (.sib 4 none 0 (.d8 96))) from
    lea_r64_effect_step 0x110813 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 96))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110803) 16 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10818 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110818 7 14) from
    mov_r64_r64_effect_step 0x110818 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110803) 21 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1081b (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [yFieldArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · x86_norm [yFieldArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · intro f; cases f <;> x86_norm [yFieldArgumentsEffect, width]
    all_goals repeat first | constructor | rfl
  · x86_norm [yFieldArgumentsEffect, width]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks
