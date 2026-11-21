import Md5.Proofs.Buffered.Update.Slices.Entry

namespace Md5.Proofs.Buffered.Update.Slices

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def remainderCountBytes : List UInt8 :=
  [0x49, 0x89, 0xde, 0x48, 0x89, 0xea, 0x48, 0xc1, 0xea, 0x06]

def remainderCountEffect (variant : Bool) (s : RamState) : Effect :=
  { rip := (pc variant 0x1003c3)
    writes := [⟨(.reg 14 : Operand 64), (.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 5 : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg 5 : Operand 64).read s)) }

theorem remainder_count_prepare {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc variant 0x1003b9))
      (codeRange (pc variant 0x1003b9) remainderCountBytes) (remainderCountEffect variant) := by
  cases variant with
  | false =>
    unfold remainderCountBytes
    md5_run_begin mov_r64_r64_effect_step 0x1003b9 0x49 0xde
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3bc (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1003bc 0x48 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1003b9) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3bf (by decide +kernel)
    md5_run_then shr_r64_imm8_effect_step 0x1003bf 0x48 0xea 6
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1003b9) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3c3 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [pc, remainderCountEffect, shiftCount]
    · x86_norm [pc, remainderCountEffect, shiftCount]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [pc, remainderCountEffect, shiftCount]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [pc, remainderCountEffect, shiftCount]
  | true =>
    unfold remainderCountBytes
    md5_run_begin mov_r64_r64_effect_step 0x101969 0x49 0xde
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x196c (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x10196c 0x48 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101969) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x196f (by decide +kernel)
    md5_run_then shr_r64_imm8_effect_step 0x10196f 0x48 0xea 6
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101969) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1973 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [pc, remainderCountEffect, shiftCount]
    · x86_norm [pc, remainderCountEffect, shiftCount]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [pc, remainderCountEffect, shiftCount]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [pc, remainderCountEffect, shiftCount]

def alignedCountBytes : List UInt8 :=
  [0x48, 0x89, 0xdd, 0x48, 0x89, 0xea, 0x48, 0xc1, 0xea, 0x06]

def alignedCountEffect (variant : Bool) (s : RamState) : Effect :=
  { rip := (pc variant 0x100427)
    writes := [⟨(.reg 5 : Operand 64), (.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg 3 : Operand 64).read s)) }

theorem aligned_count_prepare {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc variant 0x10041d))
      (codeRange (pc variant 0x10041d) alignedCountBytes) (alignedCountEffect variant) := by
  cases variant with
  | false =>
    unfold alignedCountBytes
    md5_run_begin mov_r64_r64_effect_step 0x10041d 0x48 0xdd
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x420 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x100420 0x48 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x10041d) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x423 (by decide +kernel)
    md5_run_then shr_r64_imm8_effect_step 0x100423 0x48 0xea 6
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x10041d) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x427 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [pc, alignedCountEffect, shiftCount]
    · x86_norm [pc, alignedCountEffect, shiftCount]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [pc, alignedCountEffect, shiftCount]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [pc, alignedCountEffect, shiftCount]
  | true =>
    unfold alignedCountBytes
    md5_run_begin mov_r64_r64_effect_step 0x1019cd 0x48 0xdd
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19d0 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1019d0 0x48 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1019cd) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19d3 (by decide +kernel)
    md5_run_then shr_r64_imm8_effect_step 0x1019d3 0x48 0xea 6
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1019cd) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19d7 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [pc, alignedCountEffect, shiftCount]
    · x86_norm [pc, alignedCountEffect, shiftCount]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [pc, alignedCountEffect, shiftCount]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [pc, alignedCountEffect, shiftCount]

end Md5.Proofs.Buffered.Update.Slices
