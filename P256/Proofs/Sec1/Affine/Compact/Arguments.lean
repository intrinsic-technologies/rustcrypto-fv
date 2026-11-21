import P256.Proofs.Sec1.Affine.State
import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.Encoding.Parser.CompressedRoute.Movzx
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Encoding.Parser.CompressedRoute
open P256.Proofs.SignatureFromDer.Parser.ReadSlice


def argumentBytes : List UInt8 :=
  [0x0f, 0xb6, 0xd0, 0x4c, 0x8d, 0x7c, 0x24, 0x10,
   0x4c, 0x89, 0xff, 0x4c, 0x89, 0xf6]

def argumentEffect (s : RamState) : Effect :=
  { rip := 0x110227
    writes := [⟨(.reg 2 : Operand 64), ((Operand.reg 0 : Operand 8).read s).setWidth 64⟩,
      ⟨(.reg 15 : Operand 64), stackPtr s + 16⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 16⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r14⟩] }

attribute [local x86_compose] movzxAlEffect

set_option maxHeartbeats 800000 in
theorem arguments_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110219)
      (codeRange 0x110219 argumentBytes) argumentEffect := by
  unfold argumentBytes
  slice_run_begin (show StepEffect _ _ (movzxAlEffect 0x110219 2) from
    movzx_r32_al_effect_step 0x110219 0xd0 rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1021c (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x11021c 15 (.sib 4 none 0 (.d8 16))) from
    lea_r64_effect_step 0x11021c 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 16))
      (by constructor <;> decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110219) 3 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10221 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110221 7 15) from
    mov_r64_r64_effect_step 0x110221 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110219) 8 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10224 (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x110224 6 14) from
    mov_r64_r64_effect_step 0x110224 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110219) 11 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10227 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [argumentEffect] <;> rfl
  · x86_norm [argumentEffect] <;> rfl
  · intro f; cases f <;> x86_norm [argumentEffect]
  · x86_norm [argumentEffect] <;> rfl

end P256.Proofs.Sec1.Affine.Compact
