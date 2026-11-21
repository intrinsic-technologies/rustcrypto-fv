import Md5.Proofs.Buffered.Update.Slices.Entry
import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import Md5.Proofs.MemoryRoutines.Register.Compose

namespace Md5.Proofs.Buffered.Update.Slices

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def tailPointerBytes : List UInt8 :=
  [0x48, 0x89, 0xe8, 0x48, 0xb9, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
    0x48, 0x21, 0xc8, 0x83, 0xe5, 0x3f, 0x49, 0x01, 0xc6]

def tailPointerEffect (variant : Bool) (s : RamState) : Effect :=
  let full := (.reg 5 : Operand 64).read s &&& 0x7fffffffffffffc0
  { rip := (pc variant 0x1003f3)
    writes := [⟨(.reg 0 : Operand 64), full⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg 5 : Operand 64), (((.reg 5 : Operand 32).read s) &&& 63).setWidth 64⟩,
      ⟨(.reg 14 : Operand 64), (.reg 14 : Operand 64).read s + full⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem tail_pointer_prepare {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc variant 0x1003dd))
      (codeRange (pc variant 0x1003dd) tailPointerBytes) (tailPointerEffect variant) := by
  cases variant with
  | false =>
    unfold tailPointerBytes
    md5_run_begin mov_r64_r64_effect_step 0x1003dd 0x48 0xe8
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3e0 (by decide +kernel)
    md5_run_then mov_r64_imm64_effect_step 0x1003e0 0x48 0xb9
      (by unfold RexWPrefix; decide) (by decide) 0x7fffffffffffffc0
    case sub => exact codeRange_mem_of_drop (p := 0x1003dd) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3ea (by decide +kernel)
    md5_run_then and_r64_r64_effect_step 0x1003ea 0x48 0xc8
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1003dd) 13 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3ed (by decide +kernel)
    md5_run_then and_r32_imm8_effect_step 0x1003ed 0xe5 63 (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1003dd) 16 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3f0 (by decide +kernel)
    md5_run_then add_r64_r64_effect_step 0x1003f0 0x49 0xc6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1003dd) 19 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3f3 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [tailPointerEffect]
    · x86_norm [tailPointerEffect]
      simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
    · intro i; cases i <;> x86_norm [tailPointerEffect]
    · x86_norm [tailPointerEffect]
  | true =>
    unfold tailPointerBytes
    md5_run_begin mov_r64_r64_effect_step 0x10198d 0x48 0xe8
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1990 (by decide +kernel)
    md5_run_then mov_r64_imm64_effect_step 0x101990 0x48 0xb9
      (by unfold RexWPrefix; decide) (by decide) 0x7fffffffffffffc0
    case sub => exact codeRange_mem_of_drop (p := 0x10198d) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x199a (by decide +kernel)
    md5_run_then and_r64_r64_effect_step 0x10199a 0x48 0xc8
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x10198d) 13 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x199d (by decide +kernel)
    md5_run_then and_r32_imm8_effect_step 0x10199d 0xe5 63 (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x10198d) 16 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19a0 (by decide +kernel)
    md5_run_then add_r64_r64_effect_step 0x1019a0 0x49 0xc6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x10198d) 19 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19a3 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [tailPointerEffect]
    · x86_norm [tailPointerEffect]
      simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
    · intro i; cases i <;> x86_norm [tailPointerEffect]
    · x86_norm [tailPointerEffect]

def tailCopyBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0xc0, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xf6, 0x48, 0x89, 0xea]

def tailCopyEffect (variant : Bool) (s : RamState) : Effect :=
  { rip := (pc variant 0x100409)
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 192⟩,
      ⟨(.reg 6 : Operand 64), (.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 5 : Operand 64).read s⟩] }

theorem tail_copy_prepare {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc variant 0x1003fb))
      (codeRange (pc variant 0x1003fb) tailCopyBytes) (tailCopyEffect variant) := by
  cases variant with
  | false =>
    unfold tailCopyBytes
    md5_run_begin lea_r64_effect_step 0x1003fb 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d32 192)) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x403 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x100403 0x4c 0xf6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1003fb) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x406 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x100406 0x48 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1003fb) 11 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x409 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [tailCopyEffect]
    · x86_norm [tailCopyEffect, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [tailCopyEffect]
    · x86_norm [tailCopyEffect]
  | true =>
    unfold tailCopyBytes
    md5_run_begin lea_r64_effect_step 0x1019ab 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d32 192)) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19b3 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1019b3 0x4c 0xf6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1019ab) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19b6 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1019b6 0x48 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1019ab) 11 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19b9 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [tailCopyEffect]
    · x86_norm [tailCopyEffect, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [tailCopyEffect]
    · x86_norm [tailCopyEffect]

end Md5.Proofs.Buffered.Update.Slices
