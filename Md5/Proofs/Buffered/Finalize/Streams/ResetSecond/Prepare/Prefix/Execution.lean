import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Contracts
import Md5.Proofs.Buffered.FinalizeReset.Normalize.Execution
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] movzxR32M8Effect
attribute [local x86_local] FinalizeReset.Normalize.movzxR32M8Effect_local

def prepareBytes (variant : Variant := .original) : List UInt8 :=
  match variant with
  | .original | .finalize => [0x4c, 0x8b, 0xb4, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x44, 0xf, 0xb6, 0xbc, 0x24, 0x9f, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x4c, 0x24, 0x48, 0x48, 0x8b, 0x1, 0x48, 0x8b, 0x49, 0x8, 0x48, 0x89, 0x8c, 0x24, 0xe0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0xd8, 0x0, 0x0, 0x0]
  | .discard => [0x4c, 0x8b, 0xb4, 0x24, 0xd8, 0x0, 0x0, 0x0, 0x44, 0xf, 0xb6, 0xbc, 0x24, 0xc7, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x4c, 0x24, 0x60, 0x48, 0x8b, 0x1, 0x48, 0x8b, 0x49, 0x8, 0x48, 0x89, 0x8c, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x78]

structure PreparePre (s : RamState) (variant : Variant := .original) : Prop
    extends Storage variant.toKind s where
  rip : s.RIP = match variant with
    | .original => 0x100aa2
    | .finalize => 0x101132
    | .discard => 0x101612

def prepareEffect (s : RamState) (variant : Variant := .original) : Effect where
  rip := match variant with
    | .original => 0x100acf
    | .finalize => 0x10115f
    | .discard => 0x10163c
  writes := [
    ⟨(.reg 14 : Operand 64), (.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 80)) : Operand 64).read s⟩,
    ⟨(.reg 15 : Operand 64), ((.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 63)) : Operand 8).read s).setWidth 64⟩,
    ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + BitVec.ofNat 64 (variant.toKind.contextOffset + 64)) : Operand 64).read s⟩,
    ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + BitVec.ofNat 64 (variant.toKind.contextOffset + 72)) : Operand 64).read s⟩,
    ⟨(.mem (stackPtr s + BitVec.ofNat 64 (variant.resultOffset + 8)) : Operand 64), (.mem (stackPtr s + BitVec.ofNat 64 (variant.toKind.contextOffset + 72)) : Operand 64).read s⟩,
    ⟨(.mem (stackPtr s + BitVec.ofNat 64 variant.resultOffset) : Operand 64), (.mem (stackPtr s + BitVec.ofNat 64 (variant.toKind.contextOffset + 64)) : Operand 64).read s⟩]

set_option maxHeartbeats 800000 in
theorem prepare_execution [Bindings] {variant : Variant} (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ PreparePre s variant)
      (codeRange (match variant with
        | .original => 0x100aa2 | .finalize => 0x101132 | .discard => 0x101612)
        (prepareBytes variant)) (fun s ↦ prepareEffect s variant) := by
  cases variant with
  | original =>
      unfold prepareBytes
      md5_run_begin (mov_r64_m64_effect_step 0x100aa2 0x4c
        (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 176))
        (by decide) (by decide) (by decide))
      case pre => intro s h; exact ⟨h.rip, (h.toStorage.stackWritable 176 8 (by decide)).readable⟩
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xaaa (by decide +kernel)
      md5_run_then (movzx_r_m8_rex_effect_step 0x100aaa 0x44 (by unfold RexPrefix; decide)
        32 (Or.inr rfl) (by intro seg; rfl) 7 (.sib 4 none 0 (.d32 159))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100aa2) 8 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (h.toStorage.stackWritable 159 1 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xab3 (by decide +kernel)
      md5_run_then (lea_r64_effect_step 0x100ab3 0x48 (by unfold RexWPrefix; decide)
        1 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100aa2) 17 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xab8 (by decide +kernel)
      md5_run_then (mov_r64_m64_effect_step 0x100ab8 0x48 (by unfold RexWPrefix; decide)
        0 (.base 1 .none) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100aa2) 22 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (h.toStorage.stackWritable 72 8 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xabb (by decide +kernel)
      md5_run_then (mov_r64_m64_effect_step 0x100abb 0x48 (by unfold RexWPrefix; decide)
        1 (.base 1 (.d8 8)) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100aa2) 25 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (h.toStorage.stackWritable 80 8 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xabf (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x100abf 0x48
        (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 224))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100aa2) 29 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
        refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
        · x86_norm
          exact h.toStorage.stackWritable 224 8 (by decide)
        · x86_norm
          exact h.toStorage.stackApart (offset := 224) (len := 8) (codeOffset := 0xabf) (codeLen := 8)
            (by decide) (by decide +kernel)
        · apply Effect.avoids_of_components_mem_rip
            (movM64R64Effect_components 0x100abf 1 (.sib 4 none 0 (.d32 224)) t)
          change RangeApart (stackPtr t + 224) 8 0x100aa2 45
          rw [hsp]
          exact h.toStorage.stackApart (offset := 224) (len := 8) (codeOffset := 0xaa2)
            (codeLen := 45) (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xac7 (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x100ac7 0x48
        (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 216))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100aa2) 37 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
        refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
        · x86_norm
          exact h.toStorage.stackWritable 216 8 (by decide)
        · x86_norm
          exact h.toStorage.stackApart (offset := 216) (len := 8) (codeOffset := 0xac7) (codeLen := 8)
              (by decide) (by decide +kernel)
        · apply Effect.avoids_of_components_mem_rip
            (movM64R64Effect_components 0x100ac7 0 (.sib 4 none 0 (.d32 216)) t)
          x86_norm
          change RangeApart (stackPtr t + BitVec.ofNat 64 216) 8 0x100aa2 45
          rw [hsp]
          exact h.toStorage.stackApart (offset := 216) (len := 8) (codeOffset := 0xaa2)
              (codeLen := 45) (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xacf (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, stackPtr, BitVec.add_zero]
        exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
      · intro i; cases i <;> x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, stackPtr, BitVec.add_zero]
        exact ⟨Or.inl rfl, Or.inr rfl⟩
  | finalize =>
      unfold prepareBytes
      md5_run_begin (mov_r64_m64_effect_step 0x101132 0x4c
        (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 176))
        (by decide) (by decide) (by decide))
      case pre => intro s h; exact ⟨h.rip, (h.toStorage.stackWritable 176 8 (by decide)).readable⟩
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x113a (by decide +kernel)
      md5_run_then (movzx_r_m8_rex_effect_step 0x10113a 0x44 (by unfold RexPrefix; decide)
        32 (Or.inr rfl) (by intro seg; rfl) 7 (.sib 4 none 0 (.d32 159))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101132) 8 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (h.toStorage.stackWritable 159 1 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1143 (by decide +kernel)
      md5_run_then (lea_r64_effect_step 0x101143 0x48 (by unfold RexWPrefix; decide)
        1 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101132) 17 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1148 (by decide +kernel)
      md5_run_then (mov_r64_m64_effect_step 0x101148 0x48 (by unfold RexWPrefix; decide)
        0 (.base 1 .none) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101132) 22 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (h.toStorage.stackWritable 72 8 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x114b (by decide +kernel)
      md5_run_then (mov_r64_m64_effect_step 0x10114b 0x48 (by unfold RexWPrefix; decide)
        1 (.base 1 (.d8 8)) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101132) 25 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (h.toStorage.stackWritable 80 8 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x114f (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x10114f 0x48
        (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 224))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101132) 29 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
        refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
        · x86_norm
          exact h.toStorage.stackWritable 224 8 (by decide)
        · x86_norm
          exact h.toStorage.stackApart (offset := 224) (len := 8) (codeOffset := 0x114f) (codeLen := 8)
            (by decide) (by decide +kernel)
        · apply Effect.avoids_of_components_mem_rip
            (movM64R64Effect_components 0x10114f 1 (.sib 4 none 0 (.d32 224)) t)
          change RangeApart (stackPtr t + 224) 8 0x101132 45
          rw [hsp]
          exact h.toStorage.stackApart (offset := 224) (len := 8) (codeOffset := 0x1132)
            (codeLen := 45) (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1157 (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x101157 0x48
        (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 216))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101132) 37 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
        refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
        · x86_norm
          exact h.toStorage.stackWritable 216 8 (by decide)
        · x86_norm
          exact h.toStorage.stackApart (offset := 216) (len := 8) (codeOffset := 0x1157) (codeLen := 8)
              (by decide) (by decide +kernel)
        · apply Effect.avoids_of_components_mem_rip
            (movM64R64Effect_components 0x101157 0 (.sib 4 none 0 (.d32 216)) t)
          x86_norm
          change RangeApart (stackPtr t + BitVec.ofNat 64 216) 8 0x101132 45
          rw [hsp]
          exact h.toStorage.stackApart (offset := 216) (len := 8) (codeOffset := 0x1132)
              (codeLen := 45) (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x115f (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, stackPtr, BitVec.add_zero]
        exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
      · intro i; cases i <;> x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, stackPtr, BitVec.add_zero]
        exact ⟨Or.inl rfl, Or.inr rfl⟩
  | discard =>
      unfold prepareBytes
      md5_run_begin (mov_r64_m64_effect_step 0x101612 0x4c
        (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 216))
        (by decide) (by decide) (by decide))
      case pre => intro s h; exact ⟨h.rip, (h.toStorage.stackWritable 216 8 (by decide)).readable⟩
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x161a (by decide +kernel)
      md5_run_then (movzx_r_m8_rex_effect_step 0x10161a 0x44 (by unfold RexPrefix; decide)
        32 (Or.inr rfl) (by intro seg; rfl) 7 (.sib 4 none 0 (.d32 199))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101612) 8 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (h.toStorage.stackWritable 199 1 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1623 (by decide +kernel)
      md5_run_then (lea_r64_effect_step 0x101623 0x48 (by unfold RexWPrefix; decide)
        1 (.sib 4 none 0 (.d8 96)) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101612) 17 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1628 (by decide +kernel)
      md5_run_then (mov_r64_m64_effect_step 0x101628 0x48 (by unfold RexWPrefix; decide)
        0 (.base 1 .none) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101612) 22 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (h.toStorage.stackWritable 96 8 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x162b (by decide +kernel)
      md5_run_then (mov_r64_m64_effect_step 0x10162b 0x48 (by unfold RexWPrefix; decide)
        1 (.base 1 (.d8 8)) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101612) 25 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
        · x86_norm
          exact (h.toStorage.stackWritable 104 8 (by decide)).readable
        · x86_avoid
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x162f (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x10162f 0x48
        (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 128))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101612) 29 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
        refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
        · x86_norm
          exact h.toStorage.stackWritable 128 8 (by decide)
        · x86_norm
          exact h.toStorage.stackApart (offset := 128) (len := 8) (codeOffset := 0x162f) (codeLen := 8)
            (by decide) (by decide +kernel)
        · apply Effect.avoids_of_components_mem_rip
            (movM64R64Effect_components 0x10162f 1 (.sib 4 none 0 (.d32 128)) t)
          change RangeApart (stackPtr t + 128) 8 0x101612 42
          rw [hsp]
          exact h.toStorage.stackApart (offset := 128) (len := 8) (codeOffset := 0x1612)
            (codeLen := 42) (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1637 (by decide +kernel)
      md5_run_then (Stores.mov_m64_r64_effect_step 0x101637 0x48
        (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 120))
        (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x101612) 37 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
        refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
        · x86_norm
          exact h.toStorage.stackWritable 120 8 (by decide)
        · x86_norm
          exact h.toStorage.stackApart (offset := 120) (len := 8) (codeOffset := 0x1637) (codeLen := 5)
              (by decide) (by decide +kernel)
        · apply Effect.avoids_of_components_mem_rip
            (movM64R64Effect_components 0x101637 0 (.sib 4 none 0 (.d8 120)) t)
          x86_norm
          change RangeApart (stackPtr t + BitVec.ofNat 64 120) 8 0x101612 42
          rw [hsp]
          exact h.toStorage.stackApart (offset := 120) (len := 8) (codeOffset := 0x1612)
              (codeLen := 42) (by decide) (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x163c (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, stackPtr, BitVec.add_zero]
        exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
      · intro i; cases i <;> x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [prepareEffect, Variant.tailOffset, Variant.resultOffset, Variant.toKind, Kind.contextOffset, stackPtr, BitVec.add_zero]
        exact ⟨Or.inl rfl, Or.inr rfl⟩

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
