import P256.Proofs.Sec1.Affine.Compact.Finish.ConstantsSetup

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice

def relocateBytes : List UInt8 := [0x48,0x8d,0x54,0x24,0x10,0x48,0x8d,0xb4,0x24,0x80,0x02,0,0,0xb9,9,0,0,0,0x48,0x89,0xd7]

def relocateEffect (s : RamState) : Effect :=
  { rip := 0x11055d
    writes := [⟨(.reg 2 : Operand 64), stackPtr s + 16⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 640⟩,
      ⟨(.reg 1 : Operand 64), 9⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 16⟩] }

theorem relocate_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x110548)
      (codeRange 0x110548 relocateBytes) relocateEffect := by
  unfold relocateBytes
  slice_run_begin (show StepEffect _ _ (leaR64Effect 0x110548 2 (.sib 4 none 0 (.d8 16))) from
    lea_r64_effect_step 0x110548 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1054d (by decide))
  slice_run_then (show StepEffect _ _ (leaR64Effect 0x11054d 6 (.sib 4 none 0 (.d32 640))) from
    lea_r64_effect_step 0x11054d 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 640)) (by decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110548) 5 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10555 (by decide))
  slice_run_then (show StepEffect _ _ (movR32Imm32Effect 0x110555 5 1 9) from
    mov_r32_imm32_effect_step 0x110555 0xb9 (by decide) 9)
  case sub => exact codeRange_mem_of_drop (p := 0x110548) 13 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1055a (by decide))
  slice_run_then (show StepEffect _ _ (movR64R64Effect 0x11055a 7 2) from
    mov_r64_r64_effect_step 0x11055a 0x48 0xd7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x110548) 18 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1055d (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [relocateEffect]
  · x86_norm [relocateEffect]
  · intro f; cases f <;> x86_norm [relocateEffect]
  · x86_norm [relocateEffect]

end P256.Proofs.Sec1.Affine.Compact.Finish
