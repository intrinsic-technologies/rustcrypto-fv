import Md5.Proofs.Buffered.Update.ResetFirst.Prefix
import Md5.Proofs.MemoryRoutines.Register.Compose

namespace Md5.Proofs.Buffered.ResetFirst

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def shortCopyBytes : List UInt8 :=
  [0x4a, 0x8d, 0x3c, 0x2c, 0x48, 0x83, 0xc7, 0x08, 0x4c, 0x89, 0xe6,
    0x4c, 0x89, 0xf2]

def shortCopyEffect (s : RamState) : Effect :=
  { rip := 0x10069e
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + (.reg 13 : Operand 64).read s + 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem short_copy_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100690)
      (codeRange 0x100690 shortCopyBytes) shortCopyEffect := by
  unfold shortCopyBytes
  md5_run_begin lea_r64_effect_step 0x100690 0x4a (by unfold RexWPrefix; decide)
    7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x694 (by decide +kernel)
  md5_run_then add_r64_imm8_effect_step 0x100694 0x48 0xc7 8
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100690) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x698 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100698 0x4c 0xe6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100690) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x69b (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x10069b 0x4c 0xf2
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100690) 11 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x69e (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [shortCopyEffect]
  · x86_norm [shortCopyEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [shortCopyEffect]
  · x86_norm [shortCopyEffect]

def fillCopyBytes : List UInt8 :=
  [0x4d, 0x8d, 0x34, 0x14, 0x4a, 0x8d, 0x3c, 0x2c, 0x48, 0x83, 0xc7, 0x08,
    0x4c, 0x89, 0xe6]

def fillCopyEffect (s : RamState) : Effect :=
  { rip := 0x1006fe
    writes := [⟨(.reg 14 : Operand 64), (.reg 12 : Operand 64).read s +
      (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + (.reg 13 : Operand 64).read s + 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem fill_copy_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1006ef)
      (codeRange 0x1006ef fillCopyBytes) fillCopyEffect := by
  unfold fillCopyBytes
  md5_run_begin lea_r64_effect_step 0x1006ef 0x4d (by unfold RexWPrefix; decide)
    6 (.sib 12 (some 2) 0 .none) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x6f3 (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x1006f3 0x4a (by unfold RexWPrefix; decide)
    7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1006ef) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x6f7 (by decide +kernel)
  md5_run_then add_r64_imm8_effect_step 0x1006f7 0x48 0xc7 8
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1006ef) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x6fb (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x1006fb 0x4c 0xe6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1006ef) 12 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x6fe (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [fillCopyEffect]
  · x86_norm [fillCopyEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [fillCopyEffect]
  · x86_norm [fillCopyEffect]

def tailPointerBytes : List UInt8 :=
  [0x48, 0x89, 0xd8, 0x48, 0xb9, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
    0x48, 0x21, 0xc8, 0x83, 0xe3, 0x3f, 0x49, 0x01, 0xc4]

def tailPointerEffect (s : RamState) : Effect :=
  let full := (.reg 3 : Operand 64).read s &&& 0x7fffffffffffffc0
  { rip := 0x100756
    writes := [⟨(.reg 0 : Operand 64), full⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg 3 : Operand 64), (((.reg 3 : Operand 32).read s) &&& 63).setWidth 64⟩,
      ⟨(.reg 12 : Operand 64), (.reg 12 : Operand 64).read s + full⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem tail_pointer_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100740)
      (codeRange 0x100740 tailPointerBytes) tailPointerEffect := by
  unfold tailPointerBytes
  md5_run_begin mov_r64_r64_effect_step 0x100740 0x48 0xd8
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x743 (by decide +kernel)
  md5_run_then mov_r64_imm64_effect_step 0x100743 0x48 0xb9
    (by unfold RexWPrefix; decide) (by decide) 0x7fffffffffffffc0
  case sub => exact codeRange_mem_of_drop (p := 0x100740) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x74d (by decide +kernel)
  md5_run_then and_r64_r64_effect_step 0x10074d 0x48 0xc8
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100740) 13 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x750 (by decide +kernel)
  md5_run_then and_r32_imm8_effect_step 0x100750 0xe3 63 (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100740) 16 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x753 (by decide +kernel)
  md5_run_then add_r64_r64_effect_step 0x100753 0x49 0xc4
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100740) 19 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x756 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [tailPointerEffect]
  · x86_norm [tailPointerEffect]
    simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · intro i; cases i <;> x86_norm [tailPointerEffect]
  · x86_norm [tailPointerEffect]

def tailCopyBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x08, 0x4c, 0x89, 0xe6, 0x48, 0x89, 0xda]

def tailCopyEffect (s : RamState) : Effect :=
  { rip := 0x100765
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s⟩] }

theorem tail_copy_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x10075a)
      (codeRange 0x10075a tailCopyBytes) tailCopyEffect := by
  unfold tailCopyBytes
  md5_run_begin lea_r64_effect_step 0x10075a 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x75f (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x10075f 0x4c 0xe6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x10075a) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x762 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100762 0x48 0xda
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x10075a) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x765 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [tailCopyEffect]
  · x86_norm [tailCopyEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [tailCopyEffect]
  · x86_norm [tailCopyEffect]

end Md5.Proofs.Buffered.ResetFirst
