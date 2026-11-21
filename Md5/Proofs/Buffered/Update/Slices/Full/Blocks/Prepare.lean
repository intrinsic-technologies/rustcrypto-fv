import Md5.Proofs.Buffered.Update.Slices.Entry

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

def fullCompressBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4c, 0x89, 0xf6]

def fullCompressEffect (variant : Bool) (s : RamState) : Effect where
  rip := (pc variant 0x1003d8)
  writes := [⟨(.reg 7 : Operand 64), stackPtr s + 256⟩,
    ⟨(.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩]

theorem full_compress_prepare {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc variant 0x1003cd))
      (codeRange (pc variant 0x1003cd) fullCompressBytes) (fullCompressEffect variant) := by
  cases variant with
  | false =>
    unfold fullCompressBytes
    md5_run_begin lea_r64_effect_step 0x1003cd 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d32 256)) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3d5 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1003d5 0x4c 0xf6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1003cd) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x3d8 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ he
    apply he.weaken
    · x86_norm [pc, fullCompressEffect]
    · x86_norm [pc, fullCompressEffect, stackPtr]
      exact ⟨rfl, rfl⟩
    · intro i; cases i <;> x86_norm [pc, fullCompressEffect]
    · x86_norm [pc, fullCompressEffect]
  | true =>
    unfold fullCompressBytes
    md5_run_begin lea_r64_effect_step 0x10197d 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d32 256)) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1985 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x101985 0x4c 0xf6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x10197d) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1988 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ he
    apply he.weaken
    · x86_norm [pc, fullCompressEffect]
    · x86_norm [pc, fullCompressEffect, stackPtr]
      exact ⟨rfl, rfl⟩
    · intro i; cases i <;> x86_norm [pc, fullCompressEffect]
    · x86_norm [pc, fullCompressEffect]

end Md5.Proofs.Buffered.Update.Slices
