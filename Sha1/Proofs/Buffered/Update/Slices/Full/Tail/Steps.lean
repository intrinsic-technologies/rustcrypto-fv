import Sha1.Proofs.Buffered.DigestPrepare.Position
import Sha1.Proofs.Compress.Machine.Execution
import Sha1.Proofs.MemoryRoutines.Register.Compose

namespace Sha1.Proofs.Buffered.Update.Slices.Full

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)
open Sha1.Proofs.Buffered.DigestPrepare (byteStore_rex_effect_step store_avoids_program)

def tailArithmeticBytes : List UInt8 :=
  [0x48, 0x89, 0xe8, 0x48, 0xb9, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0x7f, 0x48, 0x21, 0xc8, 0x83, 0xe5, 0x3f, 0x49, 0x01, 0xc6]

def tailArithmeticEffect (s : RamState) : Effect where
  rip := 0x101d93
  writes := [
    ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
    ⟨(.reg 0 : Operand 64), (.reg 5 : Operand 64).read s &&& 0x7fffffffffffffc0⟩,
    ⟨(.reg 5 : Operand 64), (((.reg 5 : Operand 32).read s) &&& 63).setWidth 64⟩,
    ⟨(.reg 14 : Operand 64), (.reg 14 : Operand 64).read s +
      ((.reg 5 : Operand 64).read s &&& 0x7fffffffffffffc0)⟩]
  flags := some ⟨none, none, none, none, none, none⟩

set_option maxRecDepth 2048 in
theorem tail_arithmetic [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x101d7d)
      (codeRange 0x101d7d tailArithmeticBytes) tailArithmeticEffect := by
  unfold tailArithmeticBytes
  md5_run_begin mov_r64_r64_effect_step 0x101d7d 0x48 0xe8
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d80 (by decide +kernel)
  md5_run_then mov_r64_imm64_effect_step 0x101d80 0x48 0xb9
    (by unfold RexWPrefix; decide) (by decide) 0x7fffffffffffffc0
  case sub => exact codeRange_mem_of_drop (p := 0x101d7d) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d8a (by decide +kernel)
  md5_run_then and_r64_r64_effect_step 0x101d8a 0x48 0xc8
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d7d) 13 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d8d (by decide +kernel)
  md5_run_then and_r32_imm8_effect_step 0x101d8d 0xe5 63 (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d7d) 16 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d90 (by decide +kernel)
  md5_run_then add_r64_r64_effect_step 0x101d90 0x49 0xc6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d7d) 19 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d93 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [tailArithmeticEffect]
  · x86_norm [tailArithmeticEffect]
    simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · intro i; cases i <;> x86_norm [tailArithmeticEffect]
  · x86_norm [tailArithmeticEffect]

def tailPositionEffect (s : RamState) : Effect :=
  storeEffect 0x101d93 8 (fun u ↦ stackPtr u + 279) (fun u ↦ (.reg 5 : Operand 8).read u) s

theorem tail_position [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hout : ¬ InProgram boundary.rip) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x101d93)
    (hw : MemoryRoutines.WritableRange s (stackPtr s + 279) 1) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (tailPositionEffect s).Holds s t := by
  have hstep := byteStore_rex_effect_step 0x101d93 0x40
    (by unfold RexPrefix; decide) 5 (.sib 4 none 0 (.d32 279))
    (by decide) (by decide) (by decide)
  change StepEffect (Sha1.Proofs.Common.Instructions.StorePre.StorePre 0x101d93 8
      (fun u ↦ stackPtr u + 279) 1)
    (codeRange 0x101d93 [0x40, 0x88, 0xac, 0x24, 0x17, 1, 0, 0]) tailPositionEffect at hstep
  have hb := program_text_slice hc 0x1d93 8 (by decide +kernel)
  have hne := text_address_ne_return hout 0x1d9b (by decide +kernel)
  have hp : Sha1.Proofs.Common.Instructions.StorePre.StorePre 0x101d93 8
      (fun u ↦ stackPtr u + 279) 1 s :=
    ⟨hip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩,
      rangeApart_text hw.code (by decide +kernel : 0x1d93 + 8 ≤ Extracted.textBytes.size)⟩
  obtain ⟨t, ha, ht, he⟩ := hstep.advances hr hb hp hne
  exact ⟨t, ha, ht, he.codeIn (store_avoids_program rfl (by simpa using hw.code)) hc, he⟩

def tailArgumentsBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0xd8, 0, 0, 0, 0x4c, 0x89, 0xf6, 0x48, 0x89, 0xea]

def tailArgumentsEffect (s : RamState) : Effect where
  rip := 0x101da9
  writes := [⟨(.reg 7 : Operand 64), stackPtr s + 216⟩,
    ⟨(.reg 6 : Operand 64), (.reg 14 : Operand 64).read s⟩,
    ⟨(.reg 2 : Operand 64), (.reg 5 : Operand 64).read s⟩]

theorem tail_arguments [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x101d9b)
      (codeRange 0x101d9b tailArgumentsBytes) tailArgumentsEffect := by
  unfold tailArgumentsBytes
  md5_run_begin lea_r64_effect_step 0x101d9b 0x48
    (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 216)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1da3 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x101da3 0x4c 0xf6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d9b) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1da6 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x101da6 0x48 0xea
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d9b) 11 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1da9 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [tailArgumentsEffect]
  · x86_norm [tailArgumentsEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [tailArgumentsEffect]
  · x86_norm [tailArgumentsEffect]

end Sha1.Proofs.Buffered.Update.Slices.Full
