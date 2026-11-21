import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Tactics

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

set_option maxRecDepth 1024 in
set_option maxHeartbeats 600000 in
theorem finalBlock_high {update : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := update) .finalBlock .high)
      (codeRange (Kind.partEntry .finalBlock .high (update := update)) (Kind.partBytes .finalBlock .high))
      (partEffect (update := update) .finalBlock .high) := by
  cases update with
  | false =>
    change AdvancesBlock boundary (PartPre (update := false) .finalBlock .high)
      (codeRange 0x100555 [
        0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
        0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x48,
        0x89, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0]) _
    md5_run_begin (mov_r64_m64_effect_step 0x100555 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 64)) (by decide) (by decide) (by decide))
    case pre =>
      intro s h
      exact ⟨h.rip, (h.toStorage.stackWritable 64 8 (by decide)).readable⟩
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x55a (by decide +kernel)
    slices_copy_store 0x10055a, 0x100555, 39, 5, 0, 152,
      (.sib 4 none 0 (.d32 152)), 8
    slices_copy_load 0x100562, 0x100555, 13, 0, 56
    slices_copy_store 0x100567, 0x100555, 39, 18, 0, 144,
      (.sib 4 none 0 (.d32 144)), 8
    slices_copy_load 0x10056f, 0x100555, 26, 0, 48
    slices_copy_store 0x100574, 0x100555, 39, 31, 0, 136,
      (.sib 4 none 0 (.d32 136)), 8
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength, relocated]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
      all_goals rfl
    · intro i; cases i <;> x86_norm [partEffect]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
      all_goals rfl
  | true =>
    change AdvancesBlock boundary (PartPre (update := true) .finalBlock .high)
      (codeRange 0x101b05 [
        0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
        0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x48,
        0x89, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0]) _
    md5_run_begin (mov_r64_m64_effect_step 0x101b05 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 64)) (by decide) (by decide) (by decide))
    case pre =>
      intro s h
      exact ⟨h.rip, (h.toStorage.stackWritable 64 8 (by decide)).readable⟩
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1b0a (by decide +kernel)
    slices_copy_store 0x101b0a, 0x101b05, 39, 5, 0, 152,
      (.sib 4 none 0 (.d32 152)), 8
    slices_copy_load 0x101b12, 0x101b05, 13, 0, 56
    slices_copy_store 0x101b17, 0x101b05, 39, 18, 0, 144,
      (.sib 4 none 0 (.d32 144)), 8
    slices_copy_load 0x101b1f, 0x101b05, 26, 0, 48
    slices_copy_store 0x101b24, 0x101b05, 39, 31, 0, 136,
      (.sib 4 none 0 (.d32 136)), 8
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength, relocated]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
      all_goals rfl
    · intro i; cases i <;> x86_norm [partEffect]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
      all_goals rfl
set_option maxRecDepth 1024 in
set_option maxHeartbeats 600000 in
private theorem finalBlock_low_slices [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := false) .finalBlock .low)
      (codeRange (Kind.partEntry .finalBlock .low (update := false)) (Kind.partBytes .finalBlock .low))
      (partEffect (update := false) .finalBlock .low) := by
  change AdvancesBlock boundary (PartPre (update := false) .finalBlock .low)
    (codeRange 0x10057c [
      0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
      0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x4c,
      0x24,
      0x18, 0x48, 0x89, 0x4c, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x68]) _
  md5_run_begin (mov_r64_m64_effect_step 0x10057c 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 40)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 40 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x581 (by decide +kernel)
  slices_copy_store 0x100581, 0x10057c, 43, 5, 0, 128,
    (.sib 4 none 0 (.d32 128)), 8
  slices_copy_load 0x100589, 0x10057c, 13, 0, 32
  slices_copy_store 0x10058e, 0x10057c, 43, 18, 0, 120,
    (.sib 4 none 0 (.d8 120)), 5
  slices_copy_load 0x100593, 0x10057c, 23, 0, 16
  slices_copy_load 0x100598, 0x10057c, 28, 1, 24
  slices_copy_store 0x10059d, 0x10057c, 43, 33, 1, 112,
    (.sib 4 none 0 (.d8 112)), 5
  slices_copy_store 0x1005a2, 0x10057c, 43, 38, 0, 104,
    (.sib 4 none 0 (.d8 104)), 5
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength, relocated]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]
    all_goals rfl
  · intro i; cases i <;> x86_norm [partEffect]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]
    all_goals rfl

set_option maxRecDepth 1024 in
set_option maxHeartbeats 600000 in
private theorem finalBlock_low_updateFinalizeInto [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := true) .finalBlock .low)
      (codeRange (Kind.partEntry .finalBlock .low (update := true)) (Kind.partBytes .finalBlock .low))
      (partEffect (update := true) .finalBlock .low) := by
  change AdvancesBlock boundary (PartPre (update := true) .finalBlock .low)
    (codeRange 0x101b2c [
      0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
      0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x4c,
      0x24,
      0x18, 0x48, 0x89, 0x4c, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x68]) _
  md5_run_begin (mov_r64_m64_effect_step 0x101b2c 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 40)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 40 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1b31 (by decide +kernel)
  slices_copy_store 0x101b31, 0x101b2c, 43, 5, 0, 128,
    (.sib 4 none 0 (.d32 128)), 8
  slices_copy_load 0x101b39, 0x101b2c, 13, 0, 32
  slices_copy_store 0x101b3e, 0x101b2c, 43, 18, 0, 120,
    (.sib 4 none 0 (.d8 120)), 5
  slices_copy_load 0x101b43, 0x101b2c, 23, 0, 16
  slices_copy_load 0x101b48, 0x101b2c, 28, 1, 24
  slices_copy_store 0x101b4d, 0x101b2c, 43, 33, 1, 112,
    (.sib 4 none 0 (.d8 112)), 5
  slices_copy_store 0x101b52, 0x101b2c, 43, 38, 0, 104,
    (.sib 4 none 0 (.d8 104)), 5
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength, relocated]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]
    all_goals rfl
  · intro i; cases i <;> x86_norm [partEffect]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]
    all_goals rfl

theorem finalBlock_low {update : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := update) .finalBlock .low)
      (codeRange (Kind.partEntry .finalBlock .low (update := update)) (Kind.partBytes .finalBlock .low))
      (partEffect (update := update) .finalBlock .low) := by
  cases update with
  | false => exact finalBlock_low_slices boundary hOutside
  | true => exact finalBlock_low_updateFinalizeInto boundary hOutside

set_option maxRecDepth 1024 in
set_option maxHeartbeats 600000 in
theorem finalBlock_arguments {update : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := update) .finalBlock .arguments)
      (codeRange (Kind.partEntry .finalBlock .arguments (update := update)) (Kind.partBytes .finalBlock .arguments))
      (partEffect (update := update) .finalBlock .arguments) := by
  cases update with
  | false =>
    change AdvancesBlock boundary (PartPre (update := false) .finalBlock .arguments)
      (codeRange 0x1005a7 [
        0x48, 0x89, 0xe7, 0x48, 0x8d, 0x74, 0x24, 0x68, 0xba, 0x1, 0x0, 0x0, 0x0]) _
    md5_run_begin (mov_r64_r64_effect_step 0x1005a7 0x48 0xe7
      (by unfold RexWPrefix; decide) (by decide))
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x5aa (by decide +kernel)
    md5_run_then (lea_r64_effect_step 0x1005aa 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d8 104)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x1005a7) 3 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x5af (by decide +kernel)
    md5_run_then (mov_r32_imm32_effect_step 0x1005af 0xba (by decide) 1)
    case sub => exact codeRange_mem_of_drop (p := 0x1005a7) 8 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x5b4 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength, relocated]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
      all_goals rfl
    · intro i; cases i <;> x86_norm [partEffect]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
      all_goals rfl
  | true =>
    change AdvancesBlock boundary (PartPre (update := true) .finalBlock .arguments)
      (codeRange 0x101b57 [
        0x48, 0x89, 0xe7, 0x48, 0x8d, 0x74, 0x24, 0x68, 0xba, 0x1, 0x0, 0x0, 0x0]) _
    md5_run_begin (mov_r64_r64_effect_step 0x101b57 0x48 0xe7
      (by unfold RexWPrefix; decide) (by decide))
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1b5a (by decide +kernel)
    md5_run_then (lea_r64_effect_step 0x101b5a 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d8 104)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x101b57) 3 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1b5f (by decide +kernel)
    md5_run_then (mov_r32_imm32_effect_step 0x101b5f 0xba (by decide) 1)
    case sub => exact codeRange_mem_of_drop (p := 0x101b57) 8 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1b64 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength, relocated]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
      all_goals rfl
    · intro i; cases i <;> x86_norm [partEffect]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
      all_goals rfl

end Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy
