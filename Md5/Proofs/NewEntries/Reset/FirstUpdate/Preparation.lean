import Md5.Proofs.Buffered.Update.ResetFirst.Prefix
import Md5.Proofs.MemoryRoutines.Register.Compose

namespace Md5.Proofs.NewEntries.Reset.FirstUpdate

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def shortCopyBytes : List UInt8 :=
  [0x48, 0x8d, 0x3c, 0x2c, 0x48, 0x83, 0xc7, 0x20, 0x48, 0x89, 0xde, 0x4c, 0x89, 0xf2]

def shortCopyEffect (s : RamState) : Effect :=
  { rip := 0x1013de
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + (.reg 5 : Operand 64).read s + 32⟩,
      ⟨(.reg 6 : Operand 64), (.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem short_copy_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1013d0)
      (codeRange 0x1013d0 shortCopyBytes) shortCopyEffect := by
  unfold shortCopyBytes
  md5_run_begin lea_r64_effect_step 0x1013d0 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 (some 5) 0 .none) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13d4 (by decide +kernel)
  md5_run_then add_r64_imm8_effect_step 0x1013d4 0x48 0xc7 32
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1013d0) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13d8 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x1013d8 0x48 0xde
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1013d0) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13db (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x1013db 0x4c 0xf2
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1013d0) 11 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x13de (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [shortCopyEffect]
  · x86_norm [shortCopyEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [shortCopyEffect]
  · x86_norm [shortCopyEffect]

def fillCopyBytes : List UInt8 :=
  [0x4c, 0x8d, 0x34, 0x13, 0x48, 0x8d, 0x3c, 0x2c, 0x48, 0x83, 0xc7, 0x20, 0x48, 0x89, 0xde]

def fillCopyEffect (s : RamState) : Effect :=
  { rip := 0x101437
    writes := [⟨(.reg 14 : Operand 64), (.reg 3 : Operand 64).read s +
      (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + (.reg 5 : Operand 64).read s + 32⟩,
      ⟨(.reg 6 : Operand 64), (.reg 3 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem fill_copy_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x101428)
      (codeRange 0x101428 fillCopyBytes) fillCopyEffect := by
  unfold fillCopyBytes
  md5_run_begin lea_r64_effect_step 0x101428 0x4c (by unfold RexWPrefix; decide)
    6 (.sib 3 (some 2) 0 .none) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x142c (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x10142c 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 (some 5) 0 .none) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101428) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1430 (by decide +kernel)
  md5_run_then add_r64_imm8_effect_step 0x101430 0x48 0xc7 32
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101428) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1434 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x101434 0x48 0xde
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101428) 12 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1437 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [fillCopyEffect]
  · x86_norm [fillCopyEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [fillCopyEffect]
  · x86_norm [fillCopyEffect]

def tailPointerBytes : List UInt8 :=
  [0x4c, 0x89, 0xe8, 0x48, 0xb9, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x48, 0x21, 0xc8, 0x41, 0x83, 0xe5, 0x3f, 0x48, 0x1, 0xc3]

def tailPointerEffect (s : RamState) : Effect :=
  let full := (.reg 13 : Operand 64).read s &&& 0x7fffffffffffffc0
  { rip := 0x101490
    writes := [⟨(.reg 0 : Operand 64), full⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg 13 : Operand 64), (((.reg 13 : Operand 32).read s) &&& 63).setWidth 64⟩,
      ⟨(.reg 3 : Operand 64), (.reg 3 : Operand 64).read s + full⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem tail_pointer_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x101479)
      (codeRange 0x101479 tailPointerBytes) tailPointerEffect := by
  unfold tailPointerBytes
  md5_run_begin mov_r64_r64_effect_step 0x101479 0x4c 0xe8
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x147c (by decide +kernel)
  md5_run_then mov_r64_imm64_effect_step 0x10147c 0x48 0xb9
    (by unfold RexWPrefix; decide) (by decide) 0x7fffffffffffffc0
  case sub => exact codeRange_mem_of_drop (p := 0x101479) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1486 (by decide +kernel)
  md5_run_then and_r64_r64_effect_step 0x101486 0x48 0xc8
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101479) 13 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1489 (by decide +kernel)
  md5_run_then and_r32_imm8_rex_effect_step 0x101489 0x41 0xe5 63
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101479) 16 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x148d (by decide +kernel)
  md5_run_then add_r64_r64_effect_step 0x10148d 0x48 0xc3
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101479) 20 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1490 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [tailPointerEffect]
  · x86_norm [tailPointerEffect]
    simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · intro i; cases i <;> x86_norm [tailPointerEffect]
  · x86_norm [tailPointerEffect]

def tailCopyBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x20, 0x48, 0x89, 0xde, 0x4c, 0x89, 0xea]

def tailCopyEffect (s : RamState) : Effect :=
  { rip := 0x1014a0
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 32⟩,
      ⟨(.reg 6 : Operand 64), (.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 13 : Operand 64).read s⟩] }

theorem tail_copy_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x101495)
      (codeRange 0x101495 tailCopyBytes) tailCopyEffect := by
  unfold tailCopyBytes
  md5_run_begin lea_r64_effect_step 0x101495 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 32)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x149a (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x10149a 0x48 0xde
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101495) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x149d (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x10149d 0x4c 0xea
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101495) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14a0 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [tailCopyEffect]
  · x86_norm [tailCopyEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [tailCopyEffect]
  · x86_norm [tailCopyEffect]

end Md5.Proofs.NewEntries.Reset.FirstUpdate
