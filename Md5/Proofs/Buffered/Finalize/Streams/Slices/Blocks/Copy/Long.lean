import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Tactics

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

set_option maxRecDepth 1024 in
set_option maxHeartbeats 600000 in
private theorem longTail_high_slices [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := false) .longTail .high)
      (codeRange (Kind.partEntry .longTail .high (update := false)) (Kind.partBytes .longTail .high))
      (partEffect (update := false) .longTail .high) := by
  change AdvancesBlock boundary (PartPre (update := false) .longTail .high)
    (codeRange 0x10048d [
      0x48, 0x8b, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
      0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x38, 0x48,
      0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24,
      0x88, 0x0, 0x0, 0x0]) _
  md5_run_begin (mov_r64_m64_effect_step 0x10048d 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 72 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x492 (by decide +kernel)
  slices_copy_store 0x100492, 0x10048d, 52, 5, 0, 160,
    (.sib 4 none 0 (.d32 160)), 8
  slices_copy_load 0x10049a, 0x10048d, 13, 0, 64
  slices_copy_store 0x10049f, 0x10048d, 52, 18, 0, 152,
    (.sib 4 none 0 (.d32 152)), 8
  slices_copy_load 0x1004a7, 0x10048d, 26, 0, 56
  slices_copy_store 0x1004ac, 0x10048d, 52, 31, 0, 144,
    (.sib 4 none 0 (.d32 144)), 8
  slices_copy_load 0x1004b4, 0x10048d, 39, 0, 48
  slices_copy_store 0x1004b9, 0x10048d, 52, 44, 0, 136,
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
private theorem longTail_high_updateFinalizeInto [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := true) .longTail .high)
      (codeRange (Kind.partEntry .longTail .high (update := true)) (Kind.partBytes .longTail .high))
      (partEffect (update := true) .longTail .high) := by
  change AdvancesBlock boundary (PartPre (update := true) .longTail .high)
    (codeRange 0x101a3d [
      0x48, 0x8b, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
      0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x38, 0x48,
      0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24,
      0x88, 0x0, 0x0, 0x0]) _
  md5_run_begin (mov_r64_m64_effect_step 0x101a3d 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 72 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1a42 (by decide +kernel)
  slices_copy_store 0x101a42, 0x101a3d, 52, 5, 0, 160,
    (.sib 4 none 0 (.d32 160)), 8
  slices_copy_load 0x101a4a, 0x101a3d, 13, 0, 64
  slices_copy_store 0x101a4f, 0x101a3d, 52, 18, 0, 152,
    (.sib 4 none 0 (.d32 152)), 8
  slices_copy_load 0x101a57, 0x101a3d, 26, 0, 56
  slices_copy_store 0x101a5c, 0x101a3d, 52, 31, 0, 144,
    (.sib 4 none 0 (.d32 144)), 8
  slices_copy_load 0x101a64, 0x101a3d, 39, 0, 48
  slices_copy_store 0x101a69, 0x101a3d, 52, 44, 0, 136,
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

theorem longTail_high {update : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := update) .longTail .high)
      (codeRange (Kind.partEntry .longTail .high (update := update)) (Kind.partBytes .longTail .high))
      (partEffect (update := update) .longTail .high) := by
  cases update with
  | false => exact longTail_high_slices boundary hOutside
  | true => exact longTail_high_updateFinalizeInto boundary hOutside

set_option maxRecDepth 1024 in
set_option maxHeartbeats 600000 in
private theorem longTail_low_slices [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := false) .longTail .low)
      (codeRange (Kind.partEntry .longTail .low (update := false)) (Kind.partBytes .longTail .low))
      (partEffect (update := false) .longTail .low) := by
  change AdvancesBlock boundary (PartPre (update := false) .longTail .low)
    (codeRange 0x1004c1 [
      0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
      0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x4c,
      0x24,
      0x18, 0x48, 0x89, 0x4c, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x68]) _
  md5_run_begin (mov_r64_m64_effect_step 0x1004c1 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 40)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 40 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x4c6 (by decide +kernel)
  slices_copy_store 0x1004c6, 0x1004c1, 43, 5, 0, 128,
    (.sib 4 none 0 (.d32 128)), 8
  slices_copy_load 0x1004ce, 0x1004c1, 13, 0, 32
  slices_copy_store 0x1004d3, 0x1004c1, 43, 18, 0, 120,
    (.sib 4 none 0 (.d8 120)), 5
  slices_copy_load 0x1004d8, 0x1004c1, 23, 0, 16
  slices_copy_load 0x1004dd, 0x1004c1, 28, 1, 24
  slices_copy_store 0x1004e2, 0x1004c1, 43, 33, 1, 112,
    (.sib 4 none 0 (.d8 112)), 5
  slices_copy_store 0x1004e7, 0x1004c1, 43, 38, 0, 104,
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
private theorem longTail_low_updateFinalizeInto [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := true) .longTail .low)
      (codeRange (Kind.partEntry .longTail .low (update := true)) (Kind.partBytes .longTail .low))
      (partEffect (update := true) .longTail .low) := by
  change AdvancesBlock boundary (PartPre (update := true) .longTail .low)
    (codeRange 0x101a71 [
      0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
      0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x4c,
      0x24,
      0x18, 0x48, 0x89, 0x4c, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x68]) _
  md5_run_begin (mov_r64_m64_effect_step 0x101a71 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 40)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 40 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1a76 (by decide +kernel)
  slices_copy_store 0x101a76, 0x101a71, 43, 5, 0, 128,
    (.sib 4 none 0 (.d32 128)), 8
  slices_copy_load 0x101a7e, 0x101a71, 13, 0, 32
  slices_copy_store 0x101a83, 0x101a71, 43, 18, 0, 120,
    (.sib 4 none 0 (.d8 120)), 5
  slices_copy_load 0x101a88, 0x101a71, 23, 0, 16
  slices_copy_load 0x101a8d, 0x101a71, 28, 1, 24
  slices_copy_store 0x101a92, 0x101a71, 43, 33, 1, 112,
    (.sib 4 none 0 (.d8 112)), 5
  slices_copy_store 0x101a97, 0x101a71, 43, 38, 0, 104,
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

theorem longTail_low {update : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := update) .longTail .low)
      (codeRange (Kind.partEntry .longTail .low (update := update)) (Kind.partBytes .longTail .low))
      (partEffect (update := update) .longTail .low) := by
  cases update with
  | false => exact longTail_low_slices boundary hOutside
  | true => exact longTail_low_updateFinalizeInto boundary hOutside

set_option maxRecDepth 1024 in
set_option maxHeartbeats 600000 in
theorem longTail_arguments {update : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := update) .longTail .arguments)
      (codeRange (Kind.partEntry .longTail .arguments (update := update)) (Kind.partBytes .longTail .arguments))
      (partEffect (update := update) .longTail .arguments) := by
  cases update with
  | false =>
    change AdvancesBlock boundary (PartPre (update := false) .longTail .arguments)
      (codeRange 0x1004ec [
        0x48, 0x89, 0xe7, 0x48, 0x8d, 0x74, 0x24, 0x68, 0xba, 0x1, 0x0, 0x0, 0x0]) _
    md5_run_begin (mov_r64_r64_effect_step 0x1004ec 0x48 0xe7
      (by unfold RexWPrefix; decide) (by decide))
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x4ef (by decide +kernel)
    md5_run_then (lea_r64_effect_step 0x1004ef 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d8 104)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x1004ec) 3 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x4f4 (by decide +kernel)
    md5_run_then (mov_r32_imm32_effect_step 0x1004f4 0xba (by decide) 1)
    case sub => exact codeRange_mem_of_drop (p := 0x1004ec) 8 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x4f9 (by decide +kernel)
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
    change AdvancesBlock boundary (PartPre (update := true) .longTail .arguments)
      (codeRange 0x101a9c [
        0x48, 0x89, 0xe7, 0x48, 0x8d, 0x74, 0x24, 0x68, 0xba, 0x1, 0x0, 0x0, 0x0]) _
    md5_run_begin (mov_r64_r64_effect_step 0x101a9c 0x48 0xe7
      (by unfold RexWPrefix; decide) (by decide))
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1a9f (by decide +kernel)
    md5_run_then (lea_r64_effect_step 0x101a9f 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d8 104)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x101a9c) 3 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1aa4 (by decide +kernel)
    md5_run_then (mov_r32_imm32_effect_step 0x101aa4 0xba (by decide) 1)
    case sub => exact codeRange_mem_of_drop (p := 0x101a9c) 8 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1aa9 (by decide +kernel)
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
