import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.EffectCompose.Advance
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.PreviousCopy.OrByte
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.PreviousCopy

open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field (AdvanceTriple)

def copyBytes : List UInt8 :=
  [0x48, 0x8d, 0x8c, 0x24, 0xc8, 0x01, 0x00, 0x00, 0x48, 0x8b, 0x41, 0x18, 0x48,
   0x89, 0x84, 0x1c, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8b, 0x41, 0x10, 0x48, 0x89,
   0x84, 0x1c, 0x20, 0x01, 0x00, 0x00, 0x48, 0x8b, 0x01, 0x48, 0x8b, 0x49, 0x08,
   0x48, 0x89, 0x8c, 0x1c, 0x18, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x1c, 0x10,
   0x01, 0x00, 0x00, 0x80, 0xcb, 0x20, 0x88, 0x9c, 0x24, 0x4f, 0x01, 0x00, 0x00]

def copyEffect (s : RamState) : Effect where
  rip := 0x10f6c3
  writes := [
    ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 464) : Operand 64).read s⟩,
    ⟨(.reg 0 : Operand 64), (.mem (rspOf s + 456) : Operand 64).read s⟩,
    ⟨(.reg 3 : Operand 64), 32⟩,
    ⟨(.mem (rspOf s + 296) : Operand 64), (.mem (rspOf s + 480) : Operand 64).read s⟩,
    ⟨(.mem (rspOf s + 288) : Operand 64), (.mem (rspOf s + 472) : Operand 64).read s⟩,
    ⟨(.mem (rspOf s + 280) : Operand 64), (.mem (rspOf s + 464) : Operand 64).read s⟩,
    ⟨(.mem (rspOf s + 272) : Operand 64), (.mem (rspOf s + 456) : Operand 64).read s⟩,
    ⟨(.mem (rspOf s + 335) : Operand 8), 32⟩]
  flags := some (Hkdf.Proofs.Common.Instructions.Or.orFlags (32 : BitVec 8))

structure CopyPre (s : RamState) : Prop where
  pc : s.RIP = 0x10f682
  rbx : (Operand.reg 3#5 : Operand 64).read s = 0#64
  readable : ∀ i ∈ ([456, 464, 472, 480] : List (BitVec 64)), MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ ([272, 280, 288, 296] : List (BitVec 64)), MemWritable s (rspOf s + i) 8
  apart : ∀ i ∈ ([272, 280, 288, 296] : List (BitVec 64)), RangeApart (rspOf s + i) 8 0x10f682 65
  lengthWritable : MemWritable s (rspOf s + 335) 1
  lengthApart : RangeApart (rspOf s + 335) 1 0x10f682 65

set_option maxHeartbeats 1600000 in
theorem copyRun [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyPre (codeRange 0x10f682 copyBytes) (Effect.post copyEffect) := by
  have next (off : Nat) (bound : off < 115149) :
      Extracted.textAddress + BitVec.ofNat 64 off ≠ boundary.rip :=
    boundary_ne_program outside (inProgram_of_textOffset off bound)
  advance_begin (lea_r64_effect_step 0x10f682 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 456)) (by decide) rfl rfl)
  try (case pre => exact fun _ h => h.pc)
  case next => exact fun _ _ => next 0xf68a (by decide)
  advance_then (mov_r64_m64_effect_step 0x10f68a 0x48 (by simp [RexWPrefix]) 0
    (.base 1 (.d8 24)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f682 copyBytes 8 4)
  case mid =>
    intro s t hp eff obs
    refine ⟨LoadPre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_,
      by x86_avoid, next 0xf68e (by decide)⟩
    x86_norm [BitVec.add_zero]
    exact hp.readable 480 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f68e 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 (some 3) 0 (.d32 296)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f682 copyBytes 12 8)
  case mid =>
    intro s t hp eff obs
    refine ⟨StorePre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_,
      ?_, next 0xf696 (by decide)⟩
    · x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact hp.writable 296 (by decide)
    · x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact (hp.apart 296 (by decide)).sub 12 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact hp.apart 296 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10f696 0x48 (by simp [RexWPrefix]) 0
    (.base 1 (.d8 16)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f682 copyBytes 20 4)
  case mid =>
    intro s t hp eff obs
    refine ⟨LoadPre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_,
      by x86_avoid, next 0xf69a (by decide)⟩
    x86_norm [BitVec.add_zero]
    exact hp.readable 472 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f69a 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 (some 3) 0 (.d32 288)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f682 copyBytes 24 8)
  case mid =>
    intro s t hp eff obs
    refine ⟨StorePre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_,
      ?_, next 0xf6a2 (by decide)⟩
    · x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact hp.writable 288 (by decide)
    · x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact (hp.apart 288 (by decide)).sub 24 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact hp.apart 288 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10f6a2 0x48 (by simp [RexWPrefix]) 0
    (.base 1 .none) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f682 copyBytes 32 3)
  case mid =>
    intro s t hp eff obs
    refine ⟨LoadPre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_,
      by x86_avoid, next 0xf6a5 (by decide)⟩
    x86_norm [BitVec.add_zero]
    exact hp.readable 456 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10f6a5 0x48 (by simp [RexWPrefix]) 1
    (.base 1 (.d8 8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f682 copyBytes 35 4)
  case mid =>
    intro s t hp eff obs
    refine ⟨LoadPre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_,
      by x86_avoid, next 0xf6a9 (by decide)⟩
    x86_norm [BitVec.add_zero]
    exact hp.readable 464 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f6a9 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 (some 3) 0 (.d32 280)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f682 copyBytes 39 8)
  case mid =>
    intro s t hp eff obs
    refine ⟨StorePre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_,
      ?_, next 0xf6b1 (by decide)⟩
    · x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact hp.writable 280 (by decide)
    · x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact (hp.apart 280 (by decide)).sub 39 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact hp.apart 280 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f6b1 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 (some 3) 0 (.d32 272)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f682 copyBytes 47 8)
  case mid =>
    intro s t hp eff obs
    refine ⟨StorePre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_,
      ?_, next 0xf6b9 (by decide)⟩
    · x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact hp.writable 272 (by decide)
    · x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact (hp.apart 272 (by decide)).sub 47 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact hp.apart 272 (by decide)
  advance_then (or_r8_imm8_effect_step 0x10f6b9 0xcb 32 (by decide) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x10f682 copyBytes 55 3)
  case mid =>
    intro s t hp eff obs
    exact ⟨eff.rip_of (by x86_norm), by x86_avoid, next 0xf6bc (by decide)⟩
  advance_then (mov_m8_r8_effect_step 0x10f6bc 3 (by decide)
    (.sib 4 none 0 (.d32 335)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10f682 copyBytes 58 7)
  case mid =>
    intro s t hp eff obs
    refine ⟨StorePre.of_holds eff (obs true) (by x86_norm) (by x86_addr_obs) ?_ ?_,
      ?_, next 0xf6c3 (by decide)⟩
    · x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact hp.lengthWritable
    · x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact (hp.lengthApart).sub 58 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (obs true)
      apply Effect.avoids_codeRange
      x86_norm [hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]
      exact hp.lengthApart

  apply AdvanceTriple.block_end
  intro s t hp effect
  have r8 : (Operand.reg 3#5 : Operand 8).read s = 0#8 := by
    change ((Operand.reg 3#5 : Operand 64).read s).setWidth 8 = _
    rw [hp.rbx]
    rfl
  have reg : gprNumber 0#1 0#1 (modrmRm 0xcb) = 3#5 := by decide
  have merged : mergeGPR 8 (32#8) (0#64) = 32#64 := by decide
  apply effect.weaken
  · rfl
  · x86_norm [copyEffect, hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero, reg, r8, merged]
  · intro i
    cases i <;> x86_norm [copyEffect, hp.rbx, reg, r8]
  · x86_norm [copyEffect, hp.rbx, BitVec.add_zero, BitVec.zero_shiftLeft, BitVec.shiftLeft_zero]

end Hkdf.Proofs.NewExpand.Expand.PreviousCopy
