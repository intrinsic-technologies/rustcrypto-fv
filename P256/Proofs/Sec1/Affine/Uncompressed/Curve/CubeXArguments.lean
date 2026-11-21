import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice

def cubeXArgumentsBytes : List UInt8 :=
  [0x4c, 0x8d, 0xa4, 0x24, 0x18, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x4c, 0x89, 0xf6, 0x4c, 0x89, 0xea]

def cubeXArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x110aa3
    writes := [⟨(.reg 12 : Operand 64), stackPtr s + 280⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 280⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩] }

set_option maxHeartbeats 800000 in
theorem cubeXArguments_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110a92)
      (codeRange 0x110a92 cubeXArgumentsBytes) cubeXArgumentsEffect := by
  unfold cubeXArgumentsBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x110a92 12 (.sib 4 none 0 (.d32 280))) from
    lea_r64_effect_step 0x110a92 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 280))
      (by constructor <;> decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10a9a (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110a9a 7 12) from
    mov_r64_r64_effect_step 0x110a9a 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110a92) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10a9d (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110a9d 6 14) from
    mov_r64_r64_effect_step 0x110a9d 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110a92) 11 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10aa0 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110aa0 2 13) from
    mov_r64_r64_effect_step 0x110aa0 0x4c 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110a92) 14 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10aa3 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [cubeXArgumentsEffect] <;> rfl
  · x86_norm [cubeXArgumentsEffect] <;> rfl
  · intro f; cases f <;> x86_norm [cubeXArgumentsEffect]
  · x86_norm [cubeXArgumentsEffect] <;> rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
