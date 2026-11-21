import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Buffered.FinalizeReset.Normalize.Execution
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] relocated

attribute [local x86_compose] movzxR32M8Effect
attribute [local x86_local] FinalizeReset.Normalize.movzxR32M8Effect_local

def prepareBytes : List UInt8 :=
  [0x4c, 0x8b, 0x74, 0x24, 0x60, 0x44, 0x0f, 0xb6, 0x7c, 0x24, 0x4f,
    0x48, 0x8d, 0x8c, 0x24, 0, 1, 0, 0, 0x48, 0x8b, 1,
    0x48, 0x8b, 0x49, 8, 0x48, 0x89, 0x4c, 0x24, 8, 0x48, 0x89, 4, 0x24]

structure PreparePre (s : RamState) (update : Bool := false) : Prop extends Storage (streamKind update) s where
  rip : s.RIP = (BitVec.ofNat 64 (relocated update 0x100440))

def prepareEffect (s : RamState) (update : Bool := false) : Effect where
  rip := (BitVec.ofNat 64 (relocated update 0x100463))
  writes := [
    ⟨(.reg 14 : Operand 64), (.mem (stackPtr s + 96) : Operand 64).read s⟩,
    ⟨(.reg 15 : Operand 64), ((.mem (stackPtr s + 79) : Operand 8).read s).setWidth 64⟩,
    ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 256) : Operand 64).read s⟩,
    ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 264) : Operand 64).read s⟩,
    ⟨(.mem (stackPtr s + 8) : Operand 64), (.mem (stackPtr s + 264) : Operand 64).read s⟩,
    ⟨(.mem (stackPtr s) : Operand 64), (.mem (stackPtr s + 256) : Operand 64).read s⟩]

set_option maxHeartbeats 800000 in
theorem prepare_execution {update : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PreparePre (update := update)) (codeRange (BitVec.ofNat 64 (relocated update 0x100440)) prepareBytes) (prepareEffect (update := update)) := by
  cases update
  case false =>
    unfold prepareBytes
    md5_run_begin (mov_r64_m64_effect_step (BitVec.ofNat 64 0x100440) 0x4c
      (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 96))
      (by decide) (by decide) (by decide))
    case pre => intro s h; exact ⟨h.rip, (h.toStorage.stackWritable 96 8 (by decide)).readable⟩
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x445 (by decide +kernel)
    md5_run_then (movzx_r_m8_rex_effect_step (BitVec.ofNat 64 0x100445) 0x44 (by unfold RexPrefix; decide)
      32 (Or.inr rfl) (by intro seg; rfl) 7 (.sib 4 none 0 (.d8 79))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100440)) 5 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable 79 1 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x44b (by decide +kernel)
    md5_run_then (lea_r64_effect_step (BitVec.ofNat 64 0x10044b) 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 (.d32 256)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100440)) 11 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x453 (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (BitVec.ofNat 64 0x100453) 0x48 (by unfold RexWPrefix; decide)
      0 (.base 1 .none) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100440)) 19 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable 256 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x456 (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (BitVec.ofNat 64 0x100456) 0x48 (by unfold RexWPrefix; decide)
      1 (.base 1 (.d8 8)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100440)) 22 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable 264 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x45a (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (BitVec.ofNat 64 0x10045a) 0x48
      (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d8 8))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100440)) 26 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 8 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := 8) (len := 8) (codeOffset := 0x45a)
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (BitVec.ofNat 64 0x10045a) 1 (.sib 4 none 0 (.d8 8)) t)
        change RangeApart (stackPtr t + 8) 8 (BitVec.ofNat 64 0x100440) 35
        rw [hsp]
        exact h.toStorage.stackApart (offset := 8) (len := 8) (codeOffset := 0x440)
          (codeLen := 35) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x45f (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (BitVec.ofNat 64 0x10045f) 0x48
      (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 .none)
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x100440)) 31 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 0 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := 0) (len := 8) (codeOffset := 0x45f) (codeLen := 4)
            (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (BitVec.ofNat 64 0x10045f) 0 (.sib 4 none 0 .none) t)
        x86_norm
        change RangeApart (stackPtr t + BitVec.ofNat 64 0) 8 (BitVec.ofNat 64 0x100440) 35
        rw [hsp]
        exact h.toStorage.stackApart (offset := 0) (len := 8) (codeOffset := 0x440)
            (codeLen := 35) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x463 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [prepareEffect]
    · x86_norm [prepareEffect, stackPtr, BitVec.add_zero]
      exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
    · intro i; cases i <;> x86_norm [prepareEffect]
    · x86_norm [prepareEffect, stackPtr, BitVec.add_zero]
      exact ⟨Or.inl rfl, Or.inr rfl⟩

  case true =>
    unfold prepareBytes
    md5_run_begin (mov_r64_m64_effect_step (BitVec.ofNat 64 0x1019f0) 0x4c
      (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 96))
      (by decide) (by decide) (by decide))
    case pre => intro s h; exact ⟨h.rip, (h.toStorage.stackWritable 96 8 (by decide)).readable⟩
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19f5 (by decide +kernel)
    md5_run_then (movzx_r_m8_rex_effect_step (BitVec.ofNat 64 0x1019f5) 0x44 (by unfold RexPrefix; decide)
      32 (Or.inr rfl) (by intro seg; rfl) 7 (.sib 4 none 0 (.d8 79))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x1019f0)) 5 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable 79 1 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19fb (by decide +kernel)
    md5_run_then (lea_r64_effect_step (BitVec.ofNat 64 0x1019fb) 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 (.d32 256)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x1019f0)) 11 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a03 (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (BitVec.ofNat 64 0x101a03) 0x48 (by unfold RexWPrefix; decide)
      0 (.base 1 .none) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x1019f0)) 19 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable 256 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a06 (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step (BitVec.ofNat 64 0x101a06) 0x48 (by unfold RexWPrefix; decide)
      1 (.base 1 (.d8 8)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x1019f0)) 22 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact (h.toStorage.stackWritable 264 8 (by decide)).readable
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a0a (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (BitVec.ofNat 64 0x101a0a) 0x48
      (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d8 8))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x1019f0)) 26 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 8 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := 8) (len := 8) (codeOffset := 0x1a0a)
          (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (BitVec.ofNat 64 0x101a0a) 1 (.sib 4 none 0 (.d8 8)) t)
        change RangeApart (stackPtr t + 8) 8 (BitVec.ofNat 64 0x1019f0) 35
        rw [hsp]
        exact h.toStorage.stackApart (offset := 8) (len := 8) (codeOffset := 0x19f0)
          (codeLen := 35) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a0f (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step (BitVec.ofNat 64 0x101a0f) 0x48
      (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 .none)
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x1019f0)) 31 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact h.toStorage.stackWritable 0 8 (by decide)
      · x86_norm
        exact h.toStorage.stackApart (offset := 0) (len := 8) (codeOffset := 0x1a0f) (codeLen := 4)
            (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components (BitVec.ofNat 64 0x101a0f) 0 (.sib 4 none 0 .none) t)
        x86_norm
        change RangeApart (stackPtr t + BitVec.ofNat 64 0) 8 (BitVec.ofNat 64 0x1019f0) 35
        rw [hsp]
        exact h.toStorage.stackApart (offset := 0) (len := 8) (codeOffset := 0x19f0)
            (codeLen := 35) (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1a13 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [prepareEffect]
    · x86_norm [prepareEffect, stackPtr, BitVec.add_zero]
      exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
    · intro i; cases i <;> x86_norm [prepareEffect]
    · x86_norm [prepareEffect, stackPtr, BitVec.add_zero]
      exact ⟨Or.inl rfl, Or.inr rfl⟩

end Md5.Proofs.Buffered.Finalize.Streams.Slices
