import Md5.Proofs.Buffered.FinalizeReset.Copy.Model
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.FinalizeReset.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block


local macro "copy_longTail_high" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .longTail .high s $v))
      (codeRange (($v).address 0x1007f0) (Kind.partBytes .longTail .high)) _
    unfold Kind.partBytes Kind.bytes commonBytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take, List.cons_append, List.nil_append]
    md5_run_begin (mov_r64_m64_effect_step (($v).address 0x1007f0) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide))
    case pre =>
      intro s h
      refine ⟨?_, (Export.stackWritable h.toStorage 0x40 8 (by decide)).readable⟩
      simpa [Variant.address, Kind.partEntry, Kind.entry, Kind.partOffset] using h.rip
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x7f5 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x1007f5) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1007f0)) 5 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x98 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x98 8 (0x7f5 + match ($v) with | .saved => 0 | .direct => 0x6b0) 8
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x1007f5) 0 (.sib 4 none 0 (.d32 0x98)) t)
        change RangeApart (stackPtr t + 0x98) 8 (($v).address 0x1007f0) 52
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x98 8 (0x7f0 + match ($v) with | .saved => 0 | .direct => 0x6b0) 52
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x7fd + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (($v).address 0x1007fd) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1007f0)) 13 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (Export.stackWritable h.toStorage 0x38 8 (by decide)).readable
      · x86_avoid
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x802 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x100802) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1007f0)) 18 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x90 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x90 8 (0x802 + match ($v) with | .saved => 0 | .direct => 0x6b0) 8
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x100802) 0 (.sib 4 none 0 (.d32 0x90)) t)
        change RangeApart (stackPtr t + 0x90) 8 (($v).address 0x1007f0) 52
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x90 8 (0x7f0 + match ($v) with | .saved => 0 | .direct => 0x6b0) 52
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x80a + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (($v).address 0x10080a) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1007f0)) 26 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (Export.stackWritable h.toStorage 0x30 8 (by decide)).readable
      · x86_avoid
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x80f + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x10080f) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1007f0)) 31 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x88 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x88 8 (0x80f + match ($v) with | .saved => 0 | .direct => 0x6b0) 8
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x10080f) 0 (.sib 4 none 0 (.d32 0x88)) t)
        change RangeApart (stackPtr t + 0x88) 8 (($v).address 0x1007f0) 52
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x88 8 (0x7f0 + match ($v) with | .saved => 0 | .direct => 0x6b0) 52
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x817 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (($v).address 0x100817) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1007f0)) 39 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (Export.stackWritable h.toStorage 0x28 8 (by decide)).readable
      · x86_avoid
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x81c + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x10081c) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1007f0)) 44 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x80 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x80 8 (0x81c + match ($v) with | .saved => 0 | .direct => 0x6b0) 8
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x10081c) 0 (.sib 4 none 0 (.d32 0x80)) t)
        change RangeApart (stackPtr t + 0x80) 8 (($v).address 0x1007f0) 52
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x80 8 (0x7f0 + match ($v) with | .saved => 0 | .direct => 0x6b0) 52
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x824 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [partEffect]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem longTail_high {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary ((fun s ↦ PartPre .longTail .high s variant))
      (codeRange (Kind.partEntry .longTail .high variant) (Kind.partBytes .longTail .high))
      ((fun s ↦ partEffect .longTail .high s variant)) := by
  cases variant
  · copy_longTail_high Variant.saved, boundary, hOutside
  · copy_longTail_high Variant.direct, boundary, hOutside

local macro "copy_longTail_low" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .longTail .low s $v))
      (codeRange (($v).address 0x100824) (Kind.partBytes .longTail .low)) _
    unfold Kind.partBytes Kind.bytes commonBytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take, List.cons_append, List.nil_append]
    md5_run_begin (mov_r64_m64_effect_step (($v).address 0x100824) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide))
    case pre =>
      intro s h
      refine ⟨?_, (Export.stackWritable h.toStorage 0x20 8 (by decide)).readable⟩
      simpa [Variant.address, Kind.partEntry, Kind.entry, Kind.partOffset] using h.rip
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x829 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x100829) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100824)) 5 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x78 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x78 8 (0x829 + match ($v) with | .saved => 0 | .direct => 0x6b0) 5
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x100829) 0 (.sib 4 none 0 (.d8 0x78)) t)
        change RangeApart (stackPtr t + 0x78) 8 (($v).address 0x100824) 40
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x78 8 (0x824 + match ($v) with | .saved => 0 | .direct => 0x6b0) 40
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x82e + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (($v).address 0x10082e) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100824)) 10 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (Export.stackWritable h.toStorage 0x18 8 (by decide)).readable
      · x86_avoid
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x833 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x100833) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100824)) 15 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x70 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x70 8 (0x833 + match ($v) with | .saved => 0 | .direct => 0x6b0) 5
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x100833) 0 (.sib 4 none 0 (.d8 0x70)) t)
        change RangeApart (stackPtr t + 0x70) 8 (($v).address 0x100824) 40
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x70 8 (0x824 + match ($v) with | .saved => 0 | .direct => 0x6b0) 40
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x838 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (($v).address 0x100838) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100824)) 20 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (Export.stackWritable h.toStorage 0x8 8 (by decide)).readable
      · x86_avoid
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x83d + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (($v).address 0x10083d) 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100824)) 25 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (Export.stackWritable h.toStorage 0x10 8 (by decide)).readable
      · x86_avoid
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x842 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x100842) 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100824)) 30 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x68 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x68 8 (0x842 + match ($v) with | .saved => 0 | .direct => 0x6b0) 5
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x100842) 1 (.sib 4 none 0 (.d8 0x68)) t)
        change RangeApart (stackPtr t + 0x68) 8 (($v).address 0x100824) 40
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x68 8 (0x824 + match ($v) with | .saved => 0 | .direct => 0x6b0) 40
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x847 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x100847) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100824)) 35 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x60 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x60 8 (0x847 + match ($v) with | .saved => 0 | .direct => 0x6b0) 5
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x100847) 0 (.sib 4 none 0 (.d8 0x60)) t)
        change RangeApart (stackPtr t + 0x60) 8 (($v).address 0x100824) 40
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x60 8 (0x824 + match ($v) with | .saved => 0 | .direct => 0x6b0) 40
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x84c + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [partEffect]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem longTail_low {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary ((fun s ↦ PartPre .longTail .low s variant))
      (codeRange (Kind.partEntry .longTail .low variant) (Kind.partBytes .longTail .low))
      ((fun s ↦ partEffect .longTail .low s variant)) := by
  cases variant
  · copy_longTail_low Variant.saved, boundary, hOutside
  · copy_longTail_low Variant.direct, boundary, hOutside

local macro "copy_longTail_arguments" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .longTail .arguments s $v))
      (codeRange (($v).address 0x10084c) (Kind.partBytes .longTail .arguments)) _
    unfold Kind.partBytes Kind.bytes commonBytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take, List.cons_append, List.nil_append]
    md5_run_begin (lea_r64_effect_step (($v).address 0x10084c) 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide))
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x854 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (lea_r64_effect_step (($v).address 0x100854) 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x10084c)) 8 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x859 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r32_imm32_effect_step (($v).address 0x100859) 0xba (by decide) 1)
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x10084c)) 13 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x85e + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [partEffect]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem longTail_arguments {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary ((fun s ↦ PartPre .longTail .arguments s variant))
      (codeRange (Kind.partEntry .longTail .arguments variant) (Kind.partBytes .longTail .arguments))
      ((fun s ↦ partEffect .longTail .arguments s variant)) := by
  cases variant
  · copy_longTail_arguments Variant.saved, boundary, hOutside
  · copy_longTail_arguments Variant.direct, boundary, hOutside

local macro "copy_finalBlock_high" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .finalBlock .high s $v))
      (codeRange (($v).address 0x1008b6) (Kind.partBytes .finalBlock .high)) _
    unfold Kind.partBytes Kind.bytes commonBytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take]
    md5_run_begin (mov_r64_m64_effect_step (($v).address 0x1008b6) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide))
    case pre =>
      intro s h
      refine ⟨?_, (Export.stackWritable h.toStorage 0x38 8 (by decide)).readable⟩
      simpa [Variant.address, Kind.partEntry, Kind.entry, Kind.partOffset] using h.rip
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8bb + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x1008bb) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008b6)) 5 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x90 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x90 8 (0x8bb + match ($v) with | .saved => 0 | .direct => 0x6b0) 8
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x1008bb) 0 (.sib 4 none 0 (.d32 0x90)) t)
        change RangeApart (stackPtr t + 0x90) 8 (($v).address 0x1008b6) 39
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x90 8 (0x8b6 + match ($v) with | .saved => 0 | .direct => 0x6b0) 39
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8c3 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (($v).address 0x1008c3) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008b6)) 13 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (Export.stackWritable h.toStorage 0x30 8 (by decide)).readable
      · x86_avoid
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8c8 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x1008c8) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008b6)) 18 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x88 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x88 8 (0x8c8 + match ($v) with | .saved => 0 | .direct => 0x6b0) 8
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x1008c8) 0 (.sib 4 none 0 (.d32 0x88)) t)
        change RangeApart (stackPtr t + 0x88) 8 (($v).address 0x1008b6) 39
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x88 8 (0x8b6 + match ($v) with | .saved => 0 | .direct => 0x6b0) 39
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8d0 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (($v).address 0x1008d0) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008b6)) 26 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (Export.stackWritable h.toStorage 0x28 8 (by decide)).readable
      · x86_avoid
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8d5 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x1008d5) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008b6)) 31 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x80 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x80 8 (0x8d5 + match ($v) with | .saved => 0 | .direct => 0x6b0) 8
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x1008d5) 0 (.sib 4 none 0 (.d32 0x80)) t)
        change RangeApart (stackPtr t + 0x80) 8 (($v).address 0x1008b6) 39
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x80 8 (0x8b6 + match ($v) with | .saved => 0 | .direct => 0x6b0) 39
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8dd + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [partEffect]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem finalBlock_high {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary ((fun s ↦ PartPre .finalBlock .high s variant))
      (codeRange (Kind.partEntry .finalBlock .high variant) (Kind.partBytes .finalBlock .high))
      ((fun s ↦ partEffect .finalBlock .high s variant)) := by
  cases variant
  · copy_finalBlock_high Variant.saved, boundary, hOutside
  · copy_finalBlock_high Variant.direct, boundary, hOutside

local macro "copy_finalBlock_low" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .finalBlock .low s $v))
      (codeRange (($v).address 0x1008dd) (Kind.partBytes .finalBlock .low)) _
    unfold Kind.partBytes Kind.bytes commonBytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take]
    md5_run_begin (mov_r64_m64_effect_step (($v).address 0x1008dd) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide))
    case pre =>
      intro s h
      refine ⟨?_, (Export.stackWritable h.toStorage 0x20 8 (by decide)).readable⟩
      simpa [Variant.address, Kind.partEntry, Kind.entry, Kind.partOffset] using h.rip
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8e2 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x1008e2) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008dd)) 5 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x78 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x78 8 (0x8e2 + match ($v) with | .saved => 0 | .direct => 0x6b0) 5
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x1008e2) 0 (.sib 4 none 0 (.d8 0x78)) t)
        change RangeApart (stackPtr t + 0x78) 8 (($v).address 0x1008dd) 40
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x78 8 (0x8dd + match ($v) with | .saved => 0 | .direct => 0x6b0) 40
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8e7 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (($v).address 0x1008e7) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008dd)) 10 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (Export.stackWritable h.toStorage 0x18 8 (by decide)).readable
      · x86_avoid
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8ec + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x1008ec) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008dd)) 15 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x70 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x70 8 (0x8ec + match ($v) with | .saved => 0 | .direct => 0x6b0) 5
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x1008ec) 0 (.sib 4 none 0 (.d8 0x70)) t)
        change RangeApart (stackPtr t + 0x70) 8 (($v).address 0x1008dd) 40
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x70 8 (0x8dd + match ($v) with | .saved => 0 | .direct => 0x6b0) 40
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8f1 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (($v).address 0x1008f1) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008dd)) 20 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (Export.stackWritable h.toStorage 0x8 8 (by decide)).readable
      · x86_avoid
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8f6 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (($v).address 0x1008f6) 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008dd)) 25 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (Export.stackWritable h.toStorage 0x10 8 (by decide)).readable
      · x86_avoid
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x8fb + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x1008fb) 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008dd)) 30 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x68 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x68 8 (0x8fb + match ($v) with | .saved => 0 | .direct => 0x6b0) 5
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x1008fb) 1 (.sib 4 none 0 (.d8 0x68)) t)
        change RangeApart (stackPtr t + 0x68) 8 (($v).address 0x1008dd) 40
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x68 8 (0x8dd + match ($v) with | .saved => 0 | .direct => 0x6b0) 40
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x900 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (($v).address 0x100900) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x1008dd)) 35 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0x60 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage 0x60 8 (0x900 + match ($v) with | .saved => 0 | .direct => 0x6b0) 5
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (($v).address 0x100900) 0 (.sib 4 none 0 (.d8 0x60)) t)
        change RangeApart (stackPtr t + 0x60) 8 (($v).address 0x1008dd) 40
        rw [hsp]
        exact Export.stackTextApart h.toStorage 0x60 8 (0x8dd + match ($v) with | .saved => 0 | .direct => 0x6b0) 40
          (by decide) (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x905 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [partEffect]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem finalBlock_low {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary ((fun s ↦ PartPre .finalBlock .low s variant))
      (codeRange (Kind.partEntry .finalBlock .low variant) (Kind.partBytes .finalBlock .low))
      ((fun s ↦ partEffect .finalBlock .low s variant)) := by
  cases variant
  · copy_finalBlock_low Variant.saved, boundary, hOutside
  · copy_finalBlock_low Variant.direct, boundary, hOutside

local macro "copy_finalBlock_arguments" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .finalBlock .arguments s $v))
      (codeRange (($v).address 0x100905) (Kind.partBytes .finalBlock .arguments)) _
    unfold Kind.partBytes Kind.bytes commonBytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take]
    md5_run_begin (lea_r64_effect_step (($v).address 0x100905) 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide))
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x90d + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (lea_r64_effect_step (($v).address 0x10090d) 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100905)) 8 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x912 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    md5_run_then (mov_r32_imm32_effect_step (($v).address 0x100912) 0xba (by decide) 1)
    case sub => exact codeRange_mem_of_drop (p := (($v).address 0x100905)) 13 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return $outside (0x917 + match ($v) with | .saved => 0 | .direct => 0x6b0) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [partEffect]
    · x86_norm [partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem finalBlock_arguments {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary ((fun s ↦ PartPre .finalBlock .arguments s variant))
      (codeRange (Kind.partEntry .finalBlock .arguments variant) (Kind.partBytes .finalBlock .arguments))
      ((fun s ↦ partEffect .finalBlock .arguments s variant)) := by
  cases variant
  · copy_finalBlock_arguments Variant.saved, boundary, hOutside
  · copy_finalBlock_arguments Variant.direct, boundary, hOutside

theorem part_execution {variant : Variant} [Bindings] (kind : Kind) (part : Part) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ PartPre kind part s variant)
      (codeRange (kind.partEntry part variant) (kind.partBytes part)) (fun s ↦ partEffect kind part s variant) := by
  cases kind <;> cases part
  · exact longTail_high boundary hOutside
  · exact longTail_low boundary hOutside
  · exact longTail_arguments boundary hOutside
  · exact finalBlock_high boundary hOutside
  · exact finalBlock_low boundary hOutside
  · exact finalBlock_arguments boundary hOutside

end Md5.Proofs.Buffered.FinalizeReset.Copy
