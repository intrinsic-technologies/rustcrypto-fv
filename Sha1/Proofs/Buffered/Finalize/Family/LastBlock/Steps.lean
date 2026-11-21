import Sha1.Proofs.Buffered.Finalize.Steps
import Sha1.Proofs.Buffered.Finalize.Digest.LengthBytes

namespace Sha1.Proofs.Buffered.Finalize.Family.LastBlock

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered.Finalize.Steps

def lengthValue (s : RamState) : BitVec 64 :=
  bswapSpec ((((Operand.reg 14 : Operand 32).read s) <<< 3).setWidth 64 |||
    ((Operand.reg 15 : Operand 64).read s <<< 9))

def lengthBytes : List UInt8 :=
  [0x49, 0xc1, 0xe7, 0x09, 0x41, 0xc1, 0xe6, 0x03, 0x4d, 0x09, 0xfe, 0x49, 0x0f, 0xce,
    0x4c, 0x89, 0x74, 0x24, 0x58, 0x4c, 0x89, 0xb4, 0x24, 0xb8, 0x00, 0x00, 0x00]

def lengthEffect (s : RamState) : Effect :=
  { rip := 0x101f0e
    writes := [
      ⟨(.reg 15 : Operand 64), (Operand.reg 15 : Operand 64).read s <<< 9⟩,
      ⟨(.reg 14 : Operand 64), lengthValue s⟩,
      ⟨(.mem (stackPtr s + 88) : Operand 64), lengthValue s⟩,
      ⟨(.mem (stackPtr s + 184) : Operand 64), lengthValue s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
theorem length_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .updateFinalizeCopy 0x101ef3)
      (codeRange 0x101ef3 lengthBytes) lengthEffect := by
  unfold lengthBytes
  md5_run_begin shl_r64_imm8_effect_step 0x101ef3 0x49 0xe7 9 (by unfold RexWPrefix; decide)
    (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1ef7 (by decide +kernel)
  md5_run_then shl_r32_imm8_rex_effect_step 0x101ef7 0x41 0xe6 3
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101ef3) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1efb (by decide +kernel)
  md5_run_then or_r64_r64_effect_step 0x101efb 0x4d 0xfe (by unfold RexWPrefix; decide)
    (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101ef3) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1efe (by decide +kernel)
  md5_run_then bswap_r64_effect_step 0x101efe 0x49 (by unfold RexWPrefix; decide) 0xce
    (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101ef3) 11 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1f01 (by decide +kernel)
  steps_copy_store 0x101f01, 0x101ef3, 27, 14, 0x4c, 6, 88, (.sib 4 none 0 (.d8 88)), 5
  steps_copy_store 0x101f06, 0x101ef3, 27, 19, 0x4c, 6, 184, (.sib 4 none 0 (.d32 184)), 8
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

def upperCopyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x50, 0x48, 0x89, 0x84, 0x24, 0xb0, 0x00, 0x00, 0x00, 0x48,
    0x8b, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0xa8, 0x00, 0x00, 0x00, 0x48, 0x8b,
    0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0xa0, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x44,
    0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00]

def upperCopyEffect (s : RamState) : Effect :=
  { rip := 0x101f42
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 56) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 176) : Operand 64), (.mem (stackPtr s + 80) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 168) : Operand 64), (.mem (stackPtr s + 72) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 160) : Operand 64), (.mem (stackPtr s + 64) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 152) : Operand 64), (.mem (stackPtr s + 56) : Operand 64).read s⟩ ] }

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
theorem upperCopy_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .updateFinalizeCopy 0x101f0e)
      (codeRange 0x101f0e upperCopyBytes) upperCopyEffect := by
  unfold upperCopyBytes
  md5_run_begin (mov_r64_m64_effect_step 0x101f0e 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 80)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 80 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1f13 (by decide +kernel)
  steps_copy_store 0x101f13, 0x101f0e, 52, 5, 0x48, 0, 176,
    (.sib 4 none 0 (.d32 176)), 8
  steps_copy_load 0x101f1b, 0x101f0e, 13, 0, 72
  steps_copy_store 0x101f20, 0x101f0e, 52, 18, 0x48, 0, 168,
    (.sib 4 none 0 (.d32 168)), 8
  steps_copy_load 0x101f28, 0x101f0e, 26, 0, 64
  steps_copy_store 0x101f2d, 0x101f0e, 52, 31, 0x48, 0, 160,
    (.sib 4 none 0 (.d32 160)), 8
  steps_copy_load 0x101f35, 0x101f0e, 39, 0, 56
  steps_copy_store 0x101f3a, 0x101f0e, 52, 44, 0x48, 0, 152,
    (.sib 4 none 0 (.d32 152)), 8
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [upperCopyEffect]
  · x86_norm [upperCopyEffect, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [upperCopyEffect]
  · x86_norm [upperCopyEffect, stackPtr]
    all_goals simp [Operand.read]

def lowerCopyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48,
    0x8b, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x4c, 0x24, 0x28, 0x48, 0x89, 0x8c, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00]

def lowerCopyEffect (s : RamState) : Effect :=
  { rip := 0x101f69
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 32) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 40) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 144) : Operand 64), (.mem (stackPtr s + 48) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 136) : Operand 64), (.mem (stackPtr s + 40) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 128) : Operand 64), (.mem (stackPtr s + 32) : Operand 64).read s⟩ ] }

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
theorem lowerCopy_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .updateFinalizeCopy 0x101f42)
      (codeRange 0x101f42 lowerCopyBytes) lowerCopyEffect := by
  unfold lowerCopyBytes
  md5_run_begin (mov_r64_m64_effect_step 0x101f42 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 48)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 48 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1f47 (by decide +kernel)
  steps_copy_store 0x101f47, 0x101f42, 39, 5, 0x48, 0, 144,
    (.sib 4 none 0 (.d32 144)), 8
  steps_copy_load 0x101f4f, 0x101f42, 13, 0, 32
  steps_copy_load 0x101f54, 0x101f42, 18, 1, 40
  steps_copy_store 0x101f59, 0x101f42, 39, 23, 0x48, 1, 136,
    (.sib 4 none 0 (.d32 136)), 8
  steps_copy_store 0x101f61, 0x101f42, 39, 31, 0x48, 0, 128,
    (.sib 4 none 0 (.d32 128)), 8
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [lowerCopyEffect]
  · x86_norm [lowerCopyEffect, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [lowerCopyEffect]
  · x86_norm [lowerCopyEffect, stackPtr]
    all_goals simp [Operand.read]

end Sha1.Proofs.Buffered.Finalize.Family.LastBlock
