import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice

def squareXArgumentsBytes : List UInt8 :=
  [0x4c, 0x8d, 0xb4, 0x24, 0x78, 0x1, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x10, 0x4c, 0x89, 0xf7, 0x4c, 0x89, 0xea]

def squareXArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x110a8d
    writes := [⟨(.reg 14 : Operand 64), stackPtr s + 376⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 16⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 376⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩] }

set_option maxHeartbeats 800000 in
theorem squareXArguments_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110a7a)
      (codeRange 0x110a7a squareXArgumentsBytes) squareXArgumentsEffect := by
  unfold squareXArgumentsBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x110a7a 14 (.sib 4 none 0 (.d32 376))) from
    lea_r64_effect_step 0x110a7a 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 376))
      (by constructor <;> decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10a82 (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x110a82 6 (.sib 4 none 0 (.d8 16))) from
    lea_r64_effect_step 0x110a82 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 16))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110a7a) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10a87 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110a87 7 14) from
    mov_r64_r64_effect_step 0x110a87 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110a7a) 13 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10a8a (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110a8a 2 13) from
    mov_r64_r64_effect_step 0x110a8a 0x4c 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110a7a) 16 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10a8d (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [squareXArgumentsEffect] <;> rfl
  · x86_norm [squareXArgumentsEffect] <;> rfl
  · intro f; cases f <;> x86_norm [squareXArgumentsEffect]
  · x86_norm [squareXArgumentsEffect] <;> rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
