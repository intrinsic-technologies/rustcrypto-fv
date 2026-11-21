import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice

def squareYArgumentsBytes : List UInt8 :=
  [0x48, 0x8d, 0xac, 0x24, 0x40, 0x2, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x10, 0x48, 0x89, 0xef, 0x4c, 0x89, 0xf2]

def squareYArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x110a41
    writes := [⟨(.reg 5 : Operand 64), stackPtr s + 576⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 16⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 576⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩] }

set_option maxHeartbeats 800000 in
theorem squareYArguments_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110a2e)
      (codeRange 0x110a2e squareYArgumentsBytes) squareYArgumentsEffect := by
  unfold squareYArgumentsBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x110a2e 5 (.sib 4 none 0 (.d32 576))) from
    lea_r64_effect_step 0x110a2e 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 576))
      (by constructor <;> decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10a36 (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x110a36 6 (.sib 4 none 0 (.d8 16))) from
    lea_r64_effect_step 0x110a36 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 16))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110a2e) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10a3b (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110a3b 7 5) from
    mov_r64_r64_effect_step 0x110a3b 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110a2e) 13 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10a3e (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110a3e 2 14) from
    mov_r64_r64_effect_step 0x110a3e 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110a2e) 16 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10a41 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [squareYArgumentsEffect] <;> rfl
  · x86_norm [squareYArgumentsEffect] <;> rfl
  · intro f; cases f <;> x86_norm [squareYArgumentsEffect]
  · x86_norm [squareYArgumentsEffect] <;> rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
