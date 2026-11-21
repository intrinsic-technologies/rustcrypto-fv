import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Mov.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Lea.Triple

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)

def saveBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x4c, 0x24, 0x18, 0x48, 0x8d, 0x94, 0x24, 0xc8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x2, 0x48, 0x89, 0x4a, 0x8, 0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x42, 0x10, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x42, 0x18, 0xb0, 0x1, 0x49, 0x89, 0xef, 0x48, 0x8b, 0x6c, 0x24, 0x8]

def saveEffect (s : RamState) : Effect where
  rip := 0x10f57d
  writes := [
    ⟨(.reg 0 : Operand 64), mergeGPR 8 1 (memLoad s.external (rspOf s + 40) 64)⟩,
    ⟨(.reg 1 : Operand 64), memLoad s.external (rspOf s + 24) 64⟩,
    ⟨(.reg 2 : Operand 64), rspOf s + 456⟩,
    ⟨(.reg 15 : Operand 64), s.regValue .rbp⟩,
    ⟨(.reg 5 : Operand 64), memLoad s.external (rspOf s + 8) 64⟩,
    ⟨(.mem (rspOf s + 456) : Operand 64), memLoad s.external (rspOf s + 16) 64⟩,
    ⟨(.mem (rspOf s + 464) : Operand 64), memLoad s.external (rspOf s + 24) 64⟩,
    ⟨(.mem (rspOf s + 472) : Operand 64), memLoad s.external (rspOf s + 32) 64⟩,
    ⟨(.mem (rspOf s + 480) : Operand 64), memLoad s.external (rspOf s + 40) 64⟩]

structure SavePre (s : RamState) : Prop where
  pc : s.RIP = 0x10f548
  readable : ∀ i ∈ ([8, 16, 24, 32, 40] : List (BitVec 64)), MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ ([456, 464, 472, 480] : List (BitVec 64)), MemWritable s (rspOf s + i) 8
  apart : ∀ i ∈ ([456, 464, 472, 480] : List (BitVec 64)), RangeApart (rspOf s + i) 8 0x10f548 53

set_option maxHeartbeats 800000 in
theorem saveRun [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SavePre (codeRange 0x10f548 saveBytes) (Effect.post saveEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10f548 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.pc, h.readable 16 (by decide)⟩
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xf54d (by decide))
  advance_then (mov_r64_m64_effect_step 0x10f54d 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f548 saveBytes 5 5)
  case mid =>
    intro s t hp eff obs
    refine ⟨LoadPre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hp.readable 24 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf552 (by decide))
  advance_then (lea_r64_effect_step 0x10f552 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 456)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f548 saveBytes 10 8)
  case mid =>
    intro s t hp eff obs
    refine ⟨eff.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf55a (by decide))
  advance_then (mov_m64_r64_effect_step 0x10f55a 0x48 (by simp [RexWPrefix]) 0
    (.base 2 .none) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f548 saveBytes 18 3)
  case mid =>
    intro s t hp eff obs
    refine ⟨StorePre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 456 (by decide)
    · x86_norm
      exact (hp.apart 456 (by decide)).sub 18 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 456 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf55d (by decide))
  advance_then (mov_m64_r64_effect_step 0x10f55d 0x48 (by simp [RexWPrefix]) 1
    (.base 2 (.d8 8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f548 saveBytes 21 4)
  case mid =>
    intro s t hp eff obs
    refine ⟨StorePre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 464 (by decide)
    · x86_norm
      exact (hp.apart 464 (by decide)).sub 21 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 464 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf561 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10f561 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f548 saveBytes 25 5)
  case mid =>
    intro s t hp eff obs
    refine ⟨LoadPre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hp.readable 32 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf566 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10f566 0x48 (by simp [RexWPrefix]) 0
    (.base 2 (.d8 16)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f548 saveBytes 30 4)
  case mid =>
    intro s t hp eff obs
    refine ⟨StorePre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 472 (by decide)
    · x86_norm
      exact (hp.apart 472 (by decide)).sub 30 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 472 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf56a (by decide))
  advance_then (mov_r64_m64_effect_step 0x10f56a 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f548 saveBytes 34 5)
  case mid =>
    intro s t hp eff obs
    refine ⟨LoadPre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hp.readable 40 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf56f (by decide))
  advance_then (mov_m64_r64_effect_step 0x10f56f 0x48 (by simp [RexWPrefix]) 0
    (.base 2 (.d8 24)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f548 saveBytes 39 4)
  case mid =>
    intro s t hp eff obs
    refine ⟨StorePre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 480 (by decide)
    · x86_norm
      exact (hp.apart 480 (by decide)).sub 39 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 480 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf573 (by decide))
  advance_then (mov_r8_imm8_effect_step 0x10f573 0xb0 (by decide) 1)
  try (case sub => exact codeRange_slice_subset 0x10f548 saveBytes 43 2)
  case mid =>
    intro s t hp eff obs
    refine ⟨eff.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf575 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10f575 0x49 0xef (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x10f548 saveBytes 45 3)
  case mid =>
    intro s t hp eff obs
    refine ⟨eff.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf578 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10f578 0x48 (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f548 saveBytes 48 5)
  case mid =>
    intro s t hp eff obs
    refine ⟨LoadPre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hp.readable 8 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf57d (by decide))
  advance_finish [saveEffect, BitVec.add_zero]

theorem saveRound [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (saved : SavedFrame entry s boundary length)
    (pc : s.RIP = 0x10f548) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (saveEffect s).Holds s t := by
  have offset (i : Nat) (hi : i ≤ 536) :
      rspOf s + BitVec.ofNat 64 i = stackPtr entry - BitVec.ofNat 64 (536 - i) := by
    change s.regValue .rsp + _ = _
    rw [saved.sp]
    apply BitVec.eq_sub_iff_add_eq.mpr
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le hi]
    exact BitVec.sub_add_cancel _ _
  have read (i : Nat) (hi : i ≤ 536) : MemReadable s (rspOf s + BitVec.ofNat 64 i) 8 := by
    rw [offset i hi]
    exact Common.CallFrame.stack_readable pre.call.stack saved.allocated (by omega) (by omega)
  have write (i : Nat) (hi : i ≤ 536) (aligned : i % 8 = 0) :
      MemWritable s (rspOf s + BitVec.ofNat 64 i) 8 := by
    rw [offset i hi]
    exact Common.CallFrame.stack_writable8 pre.call.stack pre.call.stackAvoid saved.allocated
      (by omega) (by omega)
  have apart (i : Nat) (hi : i ≤ 536) :
      RangeApart (rspOf s + BitVec.ofNat 64 i) 8 0x10f548 53 := by
    rw [offset i hi]
    exact Common.CallFrame.stack_codeApart (codeOffset := 0xf548) pre.call.stack
      (fun a ha hp => pre.call.stackAvoid a ha (.inl hp)) (by omega) (by omega) (by decide)
  have operands : SavePre s := by
    refine ⟨pc, ?_, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals exact read _ (by decide)
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact write _ (by decide) (by decide)
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact apart _ (by decide)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := saveRun boundary pre.call.outerBoundary s
    (supportedMachine_readyToStep saved.machine)
    (programText_slice (programLoaded_codeIn saved.loaded) 0xf548 saveBytes
      (by decide) (by decide +kernel)) operands
  exact ⟨fuel, t, run, ready, effect⟩

end Hkdf.Proofs.NewExpand.Expand
