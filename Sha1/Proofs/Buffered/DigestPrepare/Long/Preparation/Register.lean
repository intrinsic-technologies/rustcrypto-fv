import Sha1.Proofs.Buffered.DigestPrepare.Long.Contracts
import Sha1.Proofs.Compress.Machine.Execution
import Sha1.Proofs.Compress.Machine.Code
import Sha1.Proofs.Buffered.DigestPrepare.Branch
import Sha1.Proofs.MemoryRoutines.Register.Compose

namespace Sha1.Proofs.Buffered.DigestPrepare.Long

open Sha1.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)

def argumentsBytes : List UInt8 :=
  [0x4c, 0x89, 0xfa, 0x48, 0xc1, 0xea, 6, 0x49, 0xbc, 0xc0, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0x7f, 0x4d, 0x21, 0xfc, 0x41, 0x83, 0xe7, 0x3f,
    0x49, 0x01, 0xf4]

def argumentsEffect (s : RamState) : Effect :=
  { rip := 0x1000ae
    writes := [⟨(.reg 2 : Operand 64), (.reg 15 : Operand 64).read s >>> 6⟩,
      ⟨(.reg 12 : Operand 64), (0x7fffffffffffffc0 &&& (.reg 15 : Operand 64).read s) +
        (.reg 6 : Operand 64).read s⟩,
      ⟨(.reg 15 : Operand 64), (((.reg 15 : Operand 32).read s) &&& 63).setWidth 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxRecDepth 2048 in
theorem arguments_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100093)
      (codeRange 0x100093 argumentsBytes) argumentsEffect := by
  unfold argumentsBytes
  md5_run_begin mov_r64_r64_effect_step 0x100093 0x4c 0xfa
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x96 (by decide +kernel)
  md5_run_then shr_r64_imm8_effect_step 0x100096 0x48 0xea 6
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100093) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x9a (by decide +kernel)
  md5_run_then mov_r64_imm64_effect_step 0x10009a 0x49 0xbc
    (by unfold RexWPrefix; decide) (by decide) 0x7fffffffffffffc0
  case sub => exact codeRange_mem_of_drop (p := 0x100093) 7 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xa4 (by decide +kernel)
  md5_run_then and_r64_r64_effect_step 0x1000a4 0x4d 0xfc
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100093) 17 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xa7 (by decide +kernel)
  md5_run_then and_r32_imm8_rex_effect_step 0x1000a7 0x41 0xe7 63
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100093) 20 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xab (by decide +kernel)
  md5_run_then add_r64_r64_effect_step 0x1000ab 0x49 0xf4
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100093) 24 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xae (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [argumentsEffect, shiftCount]
  · x86_norm [argumentsEffect, shiftCount]
    simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · intro i; cases i <;> x86_norm [argumentsEffect, shiftCount]
  · x86_norm [argumentsEffect, shiftCount]

end Sha1.Proofs.Buffered.DigestPrepare.Long
