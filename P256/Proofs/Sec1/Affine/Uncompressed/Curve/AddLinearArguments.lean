import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice

def addLinearArgumentsBytes : List UInt8 :=
  [0x4c, 0x8d, 0xac, 0x24, 0x58, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xe6, 0x4c, 0x89, 0xf2]

def addLinearArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x110b01
    writes := [⟨(.reg 13 : Operand 64), stackPtr s + 344⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 344⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩] }

set_option maxHeartbeats 800000 in
theorem addLinearArguments_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110af0)
      (codeRange 0x110af0 addLinearArgumentsBytes) addLinearArgumentsEffect := by
  unfold addLinearArgumentsBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x110af0 13 (.sib 4 none 0 (.d32 344))) from
    lea_r64_effect_step 0x110af0 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 344))
      (by constructor <;> decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10af8 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110af8 7 13) from
    mov_r64_r64_effect_step 0x110af8 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110af0) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10afb (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110afb 6 12) from
    mov_r64_r64_effect_step 0x110afb 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110af0) 11 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10afe (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110afe 2 14) from
    mov_r64_r64_effect_step 0x110afe 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110af0) 14 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10b01 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [addLinearArgumentsEffect] <;> rfl
  · x86_norm [addLinearArgumentsEffect] <;> rfl
  · intro f; cases f <;> x86_norm [addLinearArgumentsEffect]
  · x86_norm [addLinearArgumentsEffect] <;> rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
