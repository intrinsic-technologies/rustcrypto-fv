import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy.Model
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

local macro "copy_longTail_high" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .longTail .high s $v))
      (codeRange (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c) (Kind.partBytes .longTail .high $v)) _
    unfold Kind.partBytes Kind.bytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take]
    md5_run_begin (mov_r64_m64_effect_step (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 152 | .finalize => 152 | .discard => 192))) (by decide) (by decide) (by decide))
    case pre =>
      intro s h
      exact ⟨h.rip, (h.toStorage.stackWritable (match ($v) with | .original => 152 | .finalize => 152 | .discard => 192) 8 (by decide)).readable⟩
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb01 | .finalize => 0x1191 | .discard => 0x1674) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100b01 | .finalize => 0x101191 | .discard => 0x101674) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 288 | .finalize => 288 | .discard => 280))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c)) 8 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 288 | .finalize => 288 | .discard => 280) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 288 | .finalize => 288 | .discard => 280)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb01 | .finalize => 0x1191 | .discard => 0x1674)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100b01 | .finalize => 0x101191 | .discard => 0x101674) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 288 | .finalize => 288 | .discard => 280))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 288 | .finalize => 288 | .discard => 280)) 8 (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c) 64
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 288 | .finalize => 288 | .discard => 280)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xaf9 | .finalize => 0x1189 | .discard => 0x166c)) (codeLen := 64)
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb09 | .finalize => 0x1199 | .discard => 0x167c) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (match ($v) with | .original => 0x100b09 | .finalize => 0x101199 | .discard => 0x10167c) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 144 | .finalize => 144 | .discard => 184))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c)) 16 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable (match ($v) with | .original => 144 | .finalize => 144 | .discard => 184) 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb11 | .finalize => 0x11a1 | .discard => 0x1684) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100b11 | .finalize => 0x1011a1 | .discard => 0x101684) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c)) 24 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb11 | .finalize => 0x11a1 | .discard => 0x1684)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100b11 | .finalize => 0x1011a1 | .discard => 0x101684) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272)) 8 (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c) 64
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xaf9 | .finalize => 0x1189 | .discard => 0x166c)) (codeLen := 64)
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb19 | .finalize => 0x11a9 | .discard => 0x168c) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (match ($v) with | .original => 0x100b19 | .finalize => 0x1011a9 | .discard => 0x10168c) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 136 | .finalize => 136 | .discard => 176))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c)) 32 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable (match ($v) with | .original => 136 | .finalize => 136 | .discard => 176) 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb21 | .finalize => 0x11b1 | .discard => 0x1694) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100b21 | .finalize => 0x1011b1 | .discard => 0x101694) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c)) 40 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb21 | .finalize => 0x11b1 | .discard => 0x1694)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100b21 | .finalize => 0x1011b1 | .discard => 0x101694) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264)) 8 (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c) 64
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xaf9 | .finalize => 0x1189 | .discard => 0x166c)) (codeLen := 64)
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb29 | .finalize => 0x11b9 | .discard => 0x169c) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (match ($v) with | .original => 0x100b29 | .finalize => 0x1011b9 | .discard => 0x10169c) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 128 | .finalize => 128 | .discard => 168))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c)) 48 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable (match ($v) with | .original => 128 | .finalize => 128 | .discard => 168) 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb31 | .finalize => 0x11c1 | .discard => 0x16a4) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100b31 | .finalize => 0x1011c1 | .discard => 0x1016a4) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c)) 56 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb31 | .finalize => 0x11c1 | .discard => 0x16a4)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100b31 | .finalize => 0x1011c1 | .discard => 0x1016a4) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256)) 8 (match ($v) with | .original => 0x100af9 | .finalize => 0x101189 | .discard => 0x10166c) 64
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xaf9 | .finalize => 0x1189 | .discard => 0x166c)) (codeLen := 64)
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb39 | .finalize => 0x11c9 | .discard => 0x16ac) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem longTail_high {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ PartPre .longTail .high s variant)
      (codeRange (Kind.partEntry .longTail .high variant) (Kind.partBytes .longTail .high variant))
      (fun s ↦ partEffect .longTail .high s variant) := by
  cases variant
  · copy_longTail_high Variant.original, boundary, hOutside
  · copy_longTail_high Variant.finalize, boundary, hOutside
  · copy_longTail_high Variant.discard, boundary, hOutside

local macro "copy_longTail_low" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .longTail .low s $v))
      (codeRange (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac) (Kind.partBytes .longTail .low $v)) _
    unfold Kind.partBytes Kind.bytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take]
    md5_run_begin (mov_r64_m64_effect_step (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 ((match ($v) with | .discard => .d32 (match ($v) with | .original => 120 | .finalize => 120 | .discard => 160) | _ => .d8 (match ($v) with | .original => 120 | .finalize => 120 | .discard => 160)))) (by decide) (by decide) (by decide))
    case pre =>
      intro s h
      exact ⟨h.rip, (h.toStorage.stackWritable (match ($v) with | .original => 120 | .finalize => 120 | .discard => 160) 8 (by decide)).readable⟩
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb3e | .finalize => 0x11ce | .discard => 0x16b4) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100b3e | .finalize => 0x1011ce | .discard => 0x1016b4) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac)) (match ($v) with | .original => 5 | .finalize => 5 | .discard => 8) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb3e | .finalize => 0x11ce | .discard => 0x16b4)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100b3e | .finalize => 0x1011ce | .discard => 0x1016b4) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248)) 8 (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac) (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64)
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb39 | .finalize => 0x11c9 | .discard => 0x16ac)) (codeLen := (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64))
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb46 | .finalize => 0x11d6 | .discard => 0x16bc) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (match ($v) with | .original => 0x100b46 | .finalize => 0x1011d6 | .discard => 0x1016bc) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 ((match ($v) with | .discard => .d32 (match ($v) with | .original => 112 | .finalize => 112 | .discard => 152) | _ => .d8 (match ($v) with | .original => 112 | .finalize => 112 | .discard => 152)))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac)) (match ($v) with | .original => 13 | .finalize => 13 | .discard => 16) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable (match ($v) with | .original => 112 | .finalize => 112 | .discard => 152) 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb4b | .finalize => 0x11db | .discard => 0x16c4) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100b4b | .finalize => 0x1011db | .discard => 0x1016c4) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac)) (match ($v) with | .original => 18 | .finalize => 18 | .discard => 24) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb4b | .finalize => 0x11db | .discard => 0x16c4)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100b4b | .finalize => 0x1011db | .discard => 0x1016c4) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240)) 8 (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac) (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64)
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb39 | .finalize => 0x11c9 | .discard => 0x16ac)) (codeLen := (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64))
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb53 | .finalize => 0x11e3 | .discard => 0x16cc) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (match ($v) with | .original => 0x100b53 | .finalize => 0x1011e3 | .discard => 0x1016cc) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 ((match ($v) with | .discard => .d32 (match ($v) with | .original => 96 | .finalize => 96 | .discard => 136) | _ => .d8 (match ($v) with | .original => 96 | .finalize => 96 | .discard => 136)))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac)) (match ($v) with | .original => 26 | .finalize => 26 | .discard => 32) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable (match ($v) with | .original => 96 | .finalize => 96 | .discard => 136) 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb58 | .finalize => 0x11e8 | .discard => 0x16d4) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (match ($v) with | .original => 0x100b58 | .finalize => 0x1011e8 | .discard => 0x1016d4) 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 ((match ($v) with | .discard => .d32 (match ($v) with | .original => 104 | .finalize => 104 | .discard => 144) | _ => .d8 (match ($v) with | .original => 104 | .finalize => 104 | .discard => 144)))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac)) (match ($v) with | .original => 31 | .finalize => 31 | .discard => 40) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable (match ($v) with | .original => 104 | .finalize => 104 | .discard => 144) 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb5d | .finalize => 0x11ed | .discard => 0x16dc) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100b5d | .finalize => 0x1011ed | .discard => 0x1016dc) 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 (.d32 (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac)) (match ($v) with | .original => 36 | .finalize => 36 | .discard => 48) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb5d | .finalize => 0x11ed | .discard => 0x16dc)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100b5d | .finalize => 0x1011ed | .discard => 0x1016dc) 1 (.sib 4 none 0 (.d32 (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232)) 8 (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac) (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64)
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb39 | .finalize => 0x11c9 | .discard => 0x16ac)) (codeLen := (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64))
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb65 | .finalize => 0x11f5 | .discard => 0x16e4) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100b65 | .finalize => 0x1011f5 | .discard => 0x1016e4) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac)) (match ($v) with | .original => 44 | .finalize => 44 | .discard => 56) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb65 | .finalize => 0x11f5 | .discard => 0x16e4)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100b65 | .finalize => 0x1011f5 | .discard => 0x1016e4) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224)) 8 (match ($v) with | .original => 0x100b39 | .finalize => 0x1011c9 | .discard => 0x1016ac) (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64)
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xb39 | .finalize => 0x11c9 | .discard => 0x16ac)) (codeLen := (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64))
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb6d | .finalize => 0x11fd | .discard => 0x16ec) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem longTail_low {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ PartPre .longTail .low s variant)
      (codeRange (Kind.partEntry .longTail .low variant) (Kind.partBytes .longTail .low variant))
      (fun s ↦ partEffect .longTail .low s variant) := by
  cases variant
  · copy_longTail_low Variant.original, boundary, hOutside
  · copy_longTail_low Variant.finalize, boundary, hOutside
  · copy_longTail_low Variant.discard, boundary, hOutside

local macro "copy_longTail_arguments" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .longTail .arguments s $v))
      (codeRange (match ($v) with | .original => 0x100b6d | .finalize => 0x1011fd | .discard => 0x1016ec) (Kind.partBytes .longTail .arguments $v)) _
    unfold Kind.partBytes Kind.bytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take]
    md5_run_begin (lea_r64_effect_step (match ($v) with | .original => 0x100b6d | .finalize => 0x1011fd | .discard => 0x1016ec) 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 ((match ($v) with | .discard => .d8 120 | _ => .d32 216))) (by decide) (by decide) (by decide))
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb75 | .finalize => 0x1205 | .discard => 0x16f1) (by decide +kernel)
    md5_run_then (lea_r64_effect_step (match ($v) with | .original => 0x100b75 | .finalize => 0x101205 | .discard => 0x1016f1) 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d32 (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100b6d | .finalize => 0x1011fd | .discard => 0x1016ec)) (match ($v) with | .original => 8 | .finalize => 8 | .discard => 5) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb7d | .finalize => 0x120d | .discard => 0x16f9) (by decide +kernel)
    md5_run_then (mov_r32_imm32_effect_step (match ($v) with | .original => 0x100b7d | .finalize => 0x10120d | .discard => 0x1016f9) 0xba (by decide) 1)
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100b6d | .finalize => 0x1011fd | .discard => 0x1016ec)) (match ($v) with | .original => 16 | .finalize => 16 | .discard => 13) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xb82 | .finalize => 0x1212 | .discard => 0x16fe) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem longTail_arguments {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ PartPre .longTail .arguments s variant)
      (codeRange (Kind.partEntry .longTail .arguments variant) (Kind.partBytes .longTail .arguments variant))
      (fun s ↦ partEffect .longTail .arguments s variant) := by
  cases variant
  · copy_longTail_arguments Variant.original, boundary, hOutside
  · copy_longTail_arguments Variant.finalize, boundary, hOutside
  · copy_longTail_arguments Variant.discard, boundary, hOutside

local macro "copy_finalBlock_high" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .finalBlock .high s $v))
      (codeRange (match ($v) with | .original => 0x100bea | .finalize => 0x10127a | .discard => 0x101772) (Kind.partBytes .finalBlock .high $v)) _
    unfold Kind.partBytes Kind.bytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take]
    md5_run_begin (mov_r64_m64_effect_step (match ($v) with | .original => 0x100bea | .finalize => 0x10127a | .discard => 0x101772) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 144 | .finalize => 144 | .discard => 184))) (by decide) (by decide) (by decide))
    case pre =>
      intro s h
      exact ⟨h.rip, (h.toStorage.stackWritable (match ($v) with | .original => 144 | .finalize => 144 | .discard => 184) 8 (by decide)).readable⟩
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xbf2 | .finalize => 0x1282 | .discard => 0x177a) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100bf2 | .finalize => 0x101282 | .discard => 0x10177a) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100bea | .finalize => 0x10127a | .discard => 0x101772)) 8 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xbf2 | .finalize => 0x1282 | .discard => 0x177a)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100bf2 | .finalize => 0x101282 | .discard => 0x10177a) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272)) 8 (match ($v) with | .original => 0x100bea | .finalize => 0x10127a | .discard => 0x101772) 48
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 280 | .finalize => 280 | .discard => 272)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xbea | .finalize => 0x127a | .discard => 0x1772)) (codeLen := 48)
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xbfa | .finalize => 0x128a | .discard => 0x1782) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (match ($v) with | .original => 0x100bfa | .finalize => 0x10128a | .discard => 0x101782) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 136 | .finalize => 136 | .discard => 176))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100bea | .finalize => 0x10127a | .discard => 0x101772)) 16 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable (match ($v) with | .original => 136 | .finalize => 136 | .discard => 176) 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc02 | .finalize => 0x1292 | .discard => 0x178a) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100c02 | .finalize => 0x101292 | .discard => 0x10178a) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100bea | .finalize => 0x10127a | .discard => 0x101772)) 24 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xc02 | .finalize => 0x1292 | .discard => 0x178a)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100c02 | .finalize => 0x101292 | .discard => 0x10178a) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264)) 8 (match ($v) with | .original => 0x100bea | .finalize => 0x10127a | .discard => 0x101772) 48
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 272 | .finalize => 272 | .discard => 264)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xbea | .finalize => 0x127a | .discard => 0x1772)) (codeLen := 48)
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc0a | .finalize => 0x129a | .discard => 0x1792) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (match ($v) with | .original => 0x100c0a | .finalize => 0x10129a | .discard => 0x101792) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 128 | .finalize => 128 | .discard => 168))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100bea | .finalize => 0x10127a | .discard => 0x101772)) 32 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable (match ($v) with | .original => 128 | .finalize => 128 | .discard => 168) 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc12 | .finalize => 0x12a2 | .discard => 0x179a) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100c12 | .finalize => 0x1012a2 | .discard => 0x10179a) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100bea | .finalize => 0x10127a | .discard => 0x101772)) 40 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xc12 | .finalize => 0x12a2 | .discard => 0x179a)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100c12 | .finalize => 0x1012a2 | .discard => 0x10179a) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256)) 8 (match ($v) with | .original => 0x100bea | .finalize => 0x10127a | .discard => 0x101772) 48
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 264 | .finalize => 264 | .discard => 256)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xbea | .finalize => 0x127a | .discard => 0x1772)) (codeLen := 48)
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc1a | .finalize => 0x12aa | .discard => 0x17a2) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem finalBlock_high {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ PartPre .finalBlock .high s variant)
      (codeRange (Kind.partEntry .finalBlock .high variant) (Kind.partBytes .finalBlock .high variant))
      (fun s ↦ partEffect .finalBlock .high s variant) := by
  cases variant
  · copy_finalBlock_high Variant.original, boundary, hOutside
  · copy_finalBlock_high Variant.finalize, boundary, hOutside
  · copy_finalBlock_high Variant.discard, boundary, hOutside

local macro "copy_finalBlock_low" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .finalBlock .low s $v))
      (codeRange (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2) (Kind.partBytes .finalBlock .low $v)) _
    unfold Kind.partBytes Kind.bytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take]
    md5_run_begin (mov_r64_m64_effect_step (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 ((match ($v) with | .discard => .d32 (match ($v) with | .original => 120 | .finalize => 120 | .discard => 160) | _ => .d8 (match ($v) with | .original => 120 | .finalize => 120 | .discard => 160)))) (by decide) (by decide) (by decide))
    case pre =>
      intro s h
      exact ⟨h.rip, (h.toStorage.stackWritable (match ($v) with | .original => 120 | .finalize => 120 | .discard => 160) 8 (by decide)).readable⟩
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc1f | .finalize => 0x12af | .discard => 0x17aa) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100c1f | .finalize => 0x1012af | .discard => 0x1017aa) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2)) (match ($v) with | .original => 5 | .finalize => 5 | .discard => 8) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xc1f | .finalize => 0x12af | .discard => 0x17aa)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100c1f | .finalize => 0x1012af | .discard => 0x1017aa) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248)) 8 (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2) (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64)
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 256 | .finalize => 256 | .discard => 248)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xc1a | .finalize => 0x12aa | .discard => 0x17a2)) (codeLen := (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64))
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc27 | .finalize => 0x12b7 | .discard => 0x17b2) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (match ($v) with | .original => 0x100c27 | .finalize => 0x1012b7 | .discard => 0x1017b2) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 ((match ($v) with | .discard => .d32 (match ($v) with | .original => 112 | .finalize => 112 | .discard => 152) | _ => .d8 (match ($v) with | .original => 112 | .finalize => 112 | .discard => 152)))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2)) (match ($v) with | .original => 13 | .finalize => 13 | .discard => 16) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable (match ($v) with | .original => 112 | .finalize => 112 | .discard => 152) 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc2c | .finalize => 0x12bc | .discard => 0x17ba) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100c2c | .finalize => 0x1012bc | .discard => 0x1017ba) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2)) (match ($v) with | .original => 18 | .finalize => 18 | .discard => 24) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xc2c | .finalize => 0x12bc | .discard => 0x17ba)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100c2c | .finalize => 0x1012bc | .discard => 0x1017ba) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240)) 8 (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2) (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64)
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 248 | .finalize => 248 | .discard => 240)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xc1a | .finalize => 0x12aa | .discard => 0x17a2)) (codeLen := (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64))
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc34 | .finalize => 0x12c4 | .discard => 0x17c2) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (match ($v) with | .original => 0x100c34 | .finalize => 0x1012c4 | .discard => 0x1017c2) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 ((match ($v) with | .discard => .d32 (match ($v) with | .original => 96 | .finalize => 96 | .discard => 136) | _ => .d8 (match ($v) with | .original => 96 | .finalize => 96 | .discard => 136)))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2)) (match ($v) with | .original => 26 | .finalize => 26 | .discard => 32) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable (match ($v) with | .original => 96 | .finalize => 96 | .discard => 136) 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc39 | .finalize => 0x12c9 | .discard => 0x17ca) (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (match ($v) with | .original => 0x100c39 | .finalize => 0x1012c9 | .discard => 0x1017ca) 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 ((match ($v) with | .discard => .d32 (match ($v) with | .original => 104 | .finalize => 104 | .discard => 144) | _ => .d8 (match ($v) with | .original => 104 | .finalize => 104 | .discard => 144)))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2)) (match ($v) with | .original => 31 | .finalize => 31 | .discard => 40) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable (match ($v) with | .original => 104 | .finalize => 104 | .discard => 144) 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc3e | .finalize => 0x12ce | .discard => 0x17d2) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100c3e | .finalize => 0x1012ce | .discard => 0x1017d2) 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 (.d32 (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2)) (match ($v) with | .original => 36 | .finalize => 36 | .discard => 48) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xc3e | .finalize => 0x12ce | .discard => 0x17d2)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100c3e | .finalize => 0x1012ce | .discard => 0x1017d2) 1 (.sib 4 none 0 (.d32 (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232)) 8 (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2) (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64)
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 240 | .finalize => 240 | .discard => 232)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xc1a | .finalize => 0x12aa | .discard => 0x17a2)) (codeLen := (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64))
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc46 | .finalize => 0x12d6 | .discard => 0x17da) (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (match ($v) with | .original => 0x100c46 | .finalize => 0x1012d6 | .discard => 0x1017da) 0x48 (by unfold RexWPrefix; decide)
      0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2)) (match ($v) with | .original => 44 | .finalize => 44 | .discard => 56) (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224) 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xc46 | .finalize => 0x12d6 | .discard => 0x17da)) (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (match ($v) with | .original => 0x100c46 | .finalize => 0x1012d6 | .discard => 0x1017da) 0 (.sib 4 none 0 (.d32 (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224))) t)
        change RangeApart (stackPtr t + (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224)) 8 (match ($v) with | .original => 0x100c1a | .finalize => 0x1012aa | .discard => 0x1017a2) (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64)
        rw [hsp]
        exact h.toStorage.stackApart (offset := (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224)) (len := 8)
          (codeOffset := (match ($v) with | .original => 0xc1a | .finalize => 0x12aa | .discard => 0x17a2)) (codeLen := (match ($v) with | .original => 52 | .finalize => 52 | .discard => 64))
          (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc4e | .finalize => 0x12de | .discard => 0x17e2) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem finalBlock_low {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ PartPre .finalBlock .low s variant)
      (codeRange (Kind.partEntry .finalBlock .low variant) (Kind.partBytes .finalBlock .low variant))
      (fun s ↦ partEffect .finalBlock .low s variant) := by
  cases variant
  · copy_finalBlock_low Variant.original, boundary, hOutside
  · copy_finalBlock_low Variant.finalize, boundary, hOutside
  · copy_finalBlock_low Variant.discard, boundary, hOutside

local macro "copy_finalBlock_arguments" v:term ", " b:term ", " outside:term : tactic =>
  `(tactic| (
    change AdvancesBlock $b ((fun s ↦ PartPre .finalBlock .arguments s $v))
      (codeRange (match ($v) with | .original => 0x100c4e | .finalize => 0x1012de | .discard => 0x1017e2) (Kind.partBytes .finalBlock .arguments $v)) _
    unfold Kind.partBytes Kind.bytes Kind.partOffset Kind.partLength
    simp only [List.drop, List.take]
    md5_run_begin (lea_r64_effect_step (match ($v) with | .original => 0x100c4e | .finalize => 0x1012de | .discard => 0x1017e2) 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 ((match ($v) with | .discard => .d8 120 | _ => .d32 216))) (by decide) (by decide) (by decide))
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc56 | .finalize => 0x12e6 | .discard => 0x17e7) (by decide +kernel)
    md5_run_then (lea_r64_effect_step (match ($v) with | .original => 0x100c56 | .finalize => 0x1012e6 | .discard => 0x1017e7) 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d32 (match ($v) with | .original => 232 | .finalize => 232 | .discard => 224))) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100c4e | .finalize => 0x1012de | .discard => 0x1017e2)) (match ($v) with | .original => 8 | .finalize => 8 | .discard => 5) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc5e | .finalize => 0x12ee | .discard => 0x17ef) (by decide +kernel)
    md5_run_then (mov_r32_imm32_effect_step (match ($v) with | .original => 0x100c5e | .finalize => 0x1012ee | .discard => 0x1017ef) 0xba (by decide) 1)
    case sub => exact codeRange_mem_of_drop (p := (match ($v) with | .original => 0x100c4e | .finalize => 0x1012de | .discard => 0x1017e2)) (match ($v) with | .original => 16 | .finalize => 16 | .discard => 13) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return $outside (match ($v) with | .original => 0xc63 | .finalize => 0x12f3 | .discard => 0x17f4) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset, Kind.partLength]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
      all_goals simp [Operand.read]
    · intro i; cases i <;> x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect]
    · x86_norm [Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, wordWrite, stackPtr]
))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3000000 in
theorem finalBlock_arguments {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ PartPre .finalBlock .arguments s variant)
      (codeRange (Kind.partEntry .finalBlock .arguments variant) (Kind.partBytes .finalBlock .arguments variant))
      (fun s ↦ partEffect .finalBlock .arguments s variant) := by
  cases variant
  · copy_finalBlock_arguments Variant.original, boundary, hOutside
  · copy_finalBlock_arguments Variant.finalize, boundary, hOutside
  · copy_finalBlock_arguments Variant.discard, boundary, hOutside

theorem part_execution {variant : Variant} [Bindings] (kind : Kind) (part : Part) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ PartPre kind part s variant)
      (codeRange (kind.partEntry part variant) (kind.partBytes part variant)) (fun s ↦ partEffect kind part s variant) := by
  cases kind <;> cases part
  · exact longTail_high boundary hOutside
  · exact longTail_low boundary hOutside
  · exact longTail_arguments boundary hOutside
  · exact finalBlock_high boundary hOutside
  · exact finalBlock_low boundary hOutside
  · exact finalBlock_arguments boundary hOutside

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy
