import Md5.Proofs.Buffered.Finalize.Digest.Finish.Copy.Parts
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.Finalize.Digest.Finish.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

local macro "finish_copy_load " pc:num ", " base:num ", " off:term ", " reg:term ", " src:term :
    tactic => do
  let nextOffset := Lean.quote (pc.getNat + 5 - 0x100000)
  `(tactic| (
  md5_run_then (mov_r64_m64_effect_step $pc 0x48 (by unfold RexWPrefix; decide)
    $reg (.sib 4 none 0 (.d8 $src)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $base) $off (by decide +kernel)
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact (h.toStorage.stackWritable $src 8 (by decide)).readable
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption) $nextOffset (by decide +kernel)))

local macro "finish_copy_store " pc:num ", " base:num ", " codeLen:term ", " off:term ", "
    reg:term ", " dst:term ", " am:term ", " len:num : tactic => do
  let pcOffset := Lean.quote (pc.getNat - 0x100000)
  let baseOffset := Lean.quote (base.getNat - 0x100000)
  let nextOffset := Lean.quote (pc.getNat + len.getNat - 0x100000)
  `(tactic| (
  md5_run_then (Stores.mov_m64_r64_effect_step $pc 0x48 (by unfold RexWPrefix; decide)
    $reg $am (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := $base) $off (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable $dst 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := $dst) (len := 8)
        (codeOffset := $pcOffset)
        (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip
        (movM64R64Effect_components $pc $reg $am t)
      change RangeApart (stackPtr t + $dst) 8 $base $codeLen
      rw [hsp]
      exact h.toStorage.stackApart (offset := $dst) (len := 8)
        (codeOffset := $baseOffset)
        (by decide) (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption) $nextOffset (by decide +kernel)))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 600000 in
theorem high [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .high)
      (codeRange (Part.entry .high) (Part.bytes .high)) (partEffect .high) := by
  change AdvancesBlock boundary (PartPre .high) (codeRange 0x1001f7 [
      0x48, 0x8b, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
      0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x38, 0x48,
      0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0]) _
  md5_run_begin (mov_r64_m64_effect_step 0x1001f7 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    refine ⟨?_, (h.toStorage.stackWritable 0x48 8 (by decide)).readable⟩
    simpa [Part.entry, Part.offset] using h.rip
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1fc (by decide +kernel)
  finish_copy_store 0x1001fc, 0x1001f7, 39, 5, 0, 0xa0,
    (.sib 4 none 0 (.d32 0xa0)), 8
  finish_copy_load 0x100204, 0x1001f7, 13, 0, 0x40
  finish_copy_store 0x100209, 0x1001f7, 39, 18, 0, 0x98,
    (.sib 4 none 0 (.d32 0x98)), 8
  finish_copy_load 0x100211, 0x1001f7, 26, 0, 0x38
  finish_copy_store 0x100216, 0x1001f7, 39, 31, 0, 0x90,
    (.sib 4 none 0 (.d32 0x90)), 8
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [partEffect, Part.entry, Part.offset, Part.length]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [partEffect]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 600000 in
theorem low [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .low)
      (codeRange (Part.entry .low) (Part.bytes .low)) (partEffect .low) := by
  change AdvancesBlock boundary (PartPre .low) (codeRange 0x10021e [
      0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44,
      0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48,
      0x8b, 0x4c, 0x24, 0x20, 0x48, 0x89, 0x4c, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x70]) _
  md5_run_begin (mov_r64_m64_effect_step 0x10021e 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    refine ⟨?_, (h.toStorage.stackWritable 0x30 8 (by decide)).readable⟩
    simpa [Part.entry, Part.offset] using h.rip
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x223 (by decide +kernel)
  finish_copy_store 0x100223, 0x10021e, 46, 5, 0, 0x88,
    (.sib 4 none 0 (.d32 0x88)), 8
  finish_copy_load 0x10022b, 0x10021e, 13, 0, 0x28
  finish_copy_store 0x100230, 0x10021e, 46, 18, 0, 0x80,
    (.sib 4 none 0 (.d32 0x80)), 8
  finish_copy_load 0x100238, 0x10021e, 26, 0, 0x18
  finish_copy_load 0x10023d, 0x10021e, 31, 1, 0x20
  finish_copy_store 0x100242, 0x10021e, 46, 36, 1, 0x78,
    (.sib 4 none 0 (.d8 0x78)), 5
  finish_copy_store 0x100247, 0x10021e, 46, 41, 0, 0x70,
    (.sib 4 none 0 (.d8 0x70)), 5
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [partEffect, Part.entry, Part.offset, Part.length]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [partEffect]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 500000 in
theorem arguments [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .arguments)
      (codeRange (Part.entry .arguments) (Part.bytes .arguments)) (partEffect .arguments) := by
  change AdvancesBlock boundary (PartPre .arguments)
    (codeRange 0x10024c [0x48, 0x8d, 0x7c, 0x24, 0x08,
      0x48, 0x8d, 0x74, 0x24, 0x70, 0xba, 1, 0, 0, 0]) _
  md5_run_begin (lea_r64_effect_step 0x10024c 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide))
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x251 (by decide +kernel)
  md5_run_then (lea_r64_effect_step 0x100251 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d8 112)) (by decide) (by decide) (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x10024c) 5 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x256 (by decide +kernel)
  md5_run_then (mov_r32_imm32_effect_step 0x100256 0xba (by decide) 1)
  case sub => exact codeRange_mem_of_drop (p := 0x10024c) 10 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x25b (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [partEffect, Part.entry, Part.offset, Part.length]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [partEffect]
  · x86_norm [partEffect, wordWrite, stackPtr]
    all_goals simp [Operand.read]

theorem part_execution [Bindings] (part : Part) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre part)
      (codeRange part.entry part.bytes) (partEffect part) := by
  cases part
  · exact high boundary hOutside
  · exact low boundary hOutside
  · exact arguments boundary hOutside

end Md5.Proofs.Buffered.Finalize.Digest.Finish.Copy
