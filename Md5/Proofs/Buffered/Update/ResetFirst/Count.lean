import Md5.Proofs.Buffered.Update.ResetFirst.Prefix

namespace Md5.Proofs.Buffered.ResetFirst

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def remainderCountBytes : List UInt8 :=
  [0x4d, 0x89, 0xf4, 0x48, 0x89, 0xda, 0x48, 0xc1, 0xea, 0x06]

def remainderCountEffect (s : RamState) : Effect :=
  { rip := 0x10072c
    writes := [⟨(.reg 12 : Operand 64), (.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg 3 : Operand 64).read s)) }

theorem remainder_count_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100722)
      (codeRange 0x100722 remainderCountBytes) remainderCountEffect := by
  unfold remainderCountBytes
  md5_run_begin mov_r64_r64_effect_step 0x100722 0x4d 0xf4
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x725 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100725 0x48 0xda
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100722) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x728 (by decide +kernel)
  md5_run_then shr_r64_imm8_effect_step 0x100728 0x48 0xea 6
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100722) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x72c (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [remainderCountEffect, shiftCount]
  · x86_norm [remainderCountEffect, shiftCount]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [remainderCountEffect, shiftCount]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [remainderCountEffect, shiftCount]

def alignedCountBytes : List UInt8 :=
  [0x4c, 0x89, 0xf3, 0x48, 0x89, 0xda, 0x48, 0xc1, 0xea, 0x06]

def alignedCountEffect (s : RamState) : Effect :=
  { rip := 0x100783
    writes := [⟨(.reg 3 : Operand 64), (.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg 14 : Operand 64).read s)) }

theorem aligned_count_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100779)
      (codeRange 0x100779 alignedCountBytes) alignedCountEffect := by
  unfold alignedCountBytes
  md5_run_begin mov_r64_r64_effect_step 0x100779 0x4c 0xf3
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x77c (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x10077c 0x48 0xda
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100779) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x77f (by decide +kernel)
  md5_run_then shr_r64_imm8_effect_step 0x10077f 0x48 0xea 6
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100779) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x783 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [alignedCountEffect, shiftCount]
  · x86_norm [alignedCountEffect, shiftCount]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [alignedCountEffect, shiftCount]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [alignedCountEffect, shiftCount]

def partialCompressBytes : List UInt8 :=
  [0xba, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x7c, 0x24, 0x48,
    0x48, 0x8d, 0x74, 0x24, 0x08]

def partialCompressEffect (s : RamState) : Effect :=
  { rip := 0x100718
    writes := [⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 8⟩] }

theorem partial_compress_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100709)
      (codeRange 0x100709 partialCompressBytes) partialCompressEffect := by
  unfold partialCompressBytes
  md5_run_begin mov_r32_imm32_effect_step 0x100709 0xba (by decide) 1
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x70e (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x10070e 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100709) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x713 (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x100713 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100709) 10 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x718 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [partialCompressEffect]
  · x86_norm [partialCompressEffect, stackPtr]
    simp [Operand.read]
  · intro i; cases i <;> x86_norm [partialCompressEffect]
  · x86_norm [partialCompressEffect]

def fullCompressBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x48, 0x4c, 0x89, 0xe6]

def fullCompressEffect (s : RamState) : Effect :=
  { rip := 0x10073b
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩] }

theorem full_compress_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100733)
      (codeRange 0x100733 fullCompressBytes) fullCompressEffect := by
  unfold fullCompressBytes
  md5_run_begin lea_r64_effect_step 0x100733 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x738 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100738 0x4c 0xe6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100733) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x73b (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [fullCompressEffect]
  · x86_norm [fullCompressEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [fullCompressEffect]
  · x86_norm [fullCompressEffect]

end Md5.Proofs.Buffered.ResetFirst
