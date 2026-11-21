import Md5.Proofs.Buffered.Update.Slices.Short

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] addR64Imm32Effect
attribute [local x86_local] addR64Imm32Effect_local

def fillCopyBytes : List UInt8 :=
  [0x49, 0x8d, 0x1c, 0x16, 0x4a, 0x8d, 0x3c, 0x2c, 0x48, 0x81, 0xc7, 0xc0,
    0x00, 0x00, 0x00, 0x4c, 0x89, 0xf6]

def fillCopyEffect (variant : Bool) (s : RamState) : Effect :=
  { rip := (pc variant 0x100389)
    writes := [⟨(.reg 3 : Operand 64), (.reg 14 : Operand 64).read s +
      (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + (.reg 13 : Operand 64).read s + 192⟩,
      ⟨(.reg 6 : Operand 64), (.reg 14 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem fill_copy_prepare {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc variant 0x100377))
      (codeRange (pc variant 0x100377) fillCopyBytes) (fillCopyEffect variant) := by
  cases variant with
  | false =>
    unfold fillCopyBytes
    md5_run_begin lea_r64_effect_step 0x100377 0x49 (by unfold RexWPrefix; decide)
      3 (.sib 14 (some 2) 0 .none) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x37b (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x10037b 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100377) 4 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x37f (by decide +kernel)
    md5_run_then add_r64_imm32_effect_step 0x10037f 0x48 0xc7 192
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100377) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x386 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x100386 0x4c 0xf6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100377) 15 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x389 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [pc, fillCopyEffect]
    · x86_norm [pc, fillCopyEffect, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [pc, fillCopyEffect]
    · x86_norm [pc, fillCopyEffect]
  | true =>
    unfold fillCopyBytes
    md5_run_begin lea_r64_effect_step 0x101927 0x49 (by unfold RexWPrefix; decide)
      3 (.sib 14 (some 2) 0 .none) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x192b (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x10192b 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101927) 4 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x192f (by decide +kernel)
    md5_run_then add_r64_imm32_effect_step 0x10192f 0x48 0xc7 192
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101927) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1936 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x101936 0x4c 0xf6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101927) 15 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1939 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [pc, fillCopyEffect]
    · x86_norm [pc, fillCopyEffect, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [pc, fillCopyEffect]
    · x86_norm [pc, fillCopyEffect]

def partialCompressBytes : List UInt8 :=
  [0xba, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d, 0xbc, 0x24, 0x00, 0x01, 0x00, 0x00,
    0x48, 0x8d, 0xb4, 0x24, 0xc0, 0x00, 0x00, 0x00]

def partialCompressEffect (variant : Bool) (s : RamState) : Effect :=
  { rip := (pc variant 0x1003ac)
    writes := [⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 256⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 192⟩] }

theorem partial_compress_prepare {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc variant 0x100397))
      (codeRange (pc variant 0x100397) partialCompressBytes) (partialCompressEffect variant) := by
  cases variant with
  | false =>
    unfold partialCompressBytes
    md5_run_begin mov_r32_imm32_effect_step 0x100397 0xba (by decide) 1
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x39c (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x10039c 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d32 256)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100397) 5 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3a4 (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x1003a4 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d32 192)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100397) 13 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3ac (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [pc, partialCompressEffect]
    · x86_norm [pc, partialCompressEffect, stackPtr]
      simp [Operand.read]
    · intro i; cases i <;> x86_norm [pc, partialCompressEffect]
    · x86_norm [pc, partialCompressEffect]
  | true =>
    unfold partialCompressBytes
    md5_run_begin mov_r32_imm32_effect_step 0x101947 0xba (by decide) 1
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x194c (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x10194c 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d32 256)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101947) 5 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1954 (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x101954 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d32 192)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101947) 13 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x195c (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [pc, partialCompressEffect]
    · x86_norm [pc, partialCompressEffect, stackPtr]
      simp [Operand.read]
    · intro i; cases i <;> x86_norm [pc, partialCompressEffect]
    · x86_norm [pc, partialCompressEffect]

end Md5.Proofs.Buffered.Update.Slices
