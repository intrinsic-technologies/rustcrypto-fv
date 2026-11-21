import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.Tactics
import X86Proofs.Instructions.Shl.Generated.R.Triple
import X86Proofs.Instructions.Or.Generated.RR.Triple
import X86Proofs.Instructions.Bswap.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

namespace Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

def lengthValue (s : RamState) : BitVec 64 :=
  bswapSpec ((((Operand.reg 15 : Operand 32).read s) <<< 3).setWidth 64 |||
    ((Operand.reg 12 : Operand 64).read s <<< 9))

def lengthBytes : List UInt8 :=
  [0x49, 0xc1, 0xe4, 0x9, 0x41, 0xc1, 0xe7, 0x3, 0x4d, 0x9, 0xe7, 0x49, 0xf, 0xcf, 0x4c, 0x89,
    0x7c, 0x24, 0x50, 0x4c, 0x89, 0xbc, 0x24, 0xb0, 0x0, 0x0, 0x0]

def lengthEffect (s : RamState) : Effect :=
  { rip := 0x10020d
    writes := [
      ⟨(.reg 12 : Operand 64), (Operand.reg 12 : Operand 64).read s <<< 9⟩,
      ⟨(.reg 15 : Operand 64), lengthValue s⟩,
      ⟨(.mem (stackPtr s + 80) : Operand 64), lengthValue s⟩,
      ⟨(.mem (stackPtr s + 176) : Operand 64), lengthValue s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
theorem length_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre 0x1001f2) (codeRange 0x1001f2 lengthBytes) lengthEffect := by
  unfold lengthBytes
  md5_run_begin shl_r64_imm8_effect_step 0x1001f2 0x49 0xe4 9 (by unfold RexWPrefix; decide)
    (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1f6 (by decide +kernel)
  md5_run_then shl_r32_imm8_rex_effect_step 0x1001f6 0x41 0xe7 3
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1001f2) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1fa (by decide +kernel)
  md5_run_then or_r64_r64_effect_step 0x1001fa 0x4d 0xe7 (by unfold RexWPrefix; decide)
    (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1001f2) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1fd (by decide +kernel)
  md5_run_then bswap_r64_effect_step 0x1001fd 0x49 (by unfold RexWPrefix; decide) 0xcf
    (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1001f2) 11 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x200 (by decide +kernel)
  digest_copy_store 0x100200, 0x1001f2, 27, 14, 0x4c, 7, 80, (.sib 4 none 0 (.d8 80)), 5
  digest_copy_store 0x100205, 0x1001f2, 27, 19, 0x4c, 7, 176, (.sib 4 none 0 (.d32 176)), 8
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [lengthEffect]
  · x86_norm [lengthEffect, lengthValue, stackPtr]
    have hc32 : shiftCount 32 (UInt8.toBitVec 3) = 3 := by decide
    have hc64 : shiftCount 64 (UInt8.toBitVec 9) = 9 := by decide
    simp only [hc32, hc64]
    repeat' apply And.intro
    all_goals first | rfl | (left; exact ⟨rfl, rfl⟩) | (right; exact ⟨rfl, rfl⟩)
  · intro i; cases i <;> x86_norm [lengthEffect]
  · x86_norm [lengthEffect, stackPtr]
    all_goals simp [Operand.read]

def argumentBytes : List UInt8 :=
  [0x48, 0x89, 0xe7, 0x48, 0x8d, 0x74, 0x24, 0x78, 0xba, 0x1, 0x0, 0x0, 0x0]

def argumentEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 13
    writes := [⟨(.reg 7 : Operand 64), stackPtr s⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 120⟩,
      ⟨(.reg 2 : Operand 64), 1⟩] }

set_option maxRecDepth 1024 in
theorem longArguments_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1001a1) (codeRange 0x1001a1 argumentBytes)
      (argumentEffect 0x1001a1) := by
  unfold argumentBytes
  md5_run_begin mov_r64_r64_effect_step 0x1001a1 0x48 0xe7 (by unfold RexWPrefix; decide)
    (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a4 (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x1001a4 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d8 120)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1001a1) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a9 (by decide +kernel)
  md5_run_then mov_r32_imm32_effect_step 0x1001a9 0xba (by decide) 1
  case sub => exact codeRange_mem_of_drop (p := 0x1001a1) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1ae (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [argumentEffect]
  · x86_norm [argumentEffect, stackPtr]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [argumentEffect]
  · x86_norm [argumentEffect, stackPtr]

set_option maxRecDepth 1024 in
theorem finalArguments_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100265) (codeRange 0x100265 argumentBytes)
      (argumentEffect 0x100265) := by
  unfold argumentBytes
  md5_run_begin mov_r64_r64_effect_step 0x100265 0x48 0xe7 (by unfold RexWPrefix; decide)
    (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x268 (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x100268 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d8 120)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100265) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x26d (by decide +kernel)
  md5_run_then mov_r32_imm32_effect_step 0x10026d 0xba (by decide) 1
  case sub => exact codeRange_mem_of_drop (p := 0x100265) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x272 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [argumentEffect]
  · x86_norm [argumentEffect, stackPtr]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [argumentEffect]
  · x86_norm [argumentEffect, stackPtr]

end Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy
