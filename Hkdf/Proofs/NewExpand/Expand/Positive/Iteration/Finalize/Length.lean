import Hkdf.Proofs.Common.StreamPadding.Stages.ZeroLength

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.Instructions
open Hkdf.Proofs.Common.Instructions.Or Hkdf.Proofs.Common.Instructions.ShiftLeft
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field (AdvanceTriple)

private def lengthBytes : List UInt8 :=
  [0x49,0xc1,0xe5,9,0x41,0xc1,0xe7,3,0x4d,9,0xef,0x49,0x0f,0xcf,
    0x4c,0x89,0xbc,0x24,0x88,0,0,0,0x4c,0x89,0x7c,0x24,0x48]

def lengthWord (s : RamState) : BitVec 64 :=
  bswap64 ((((.reg 15 : Operand 32).read s <<< 3).setWidth 64) ||| ((.reg 13 : Operand 64).read s <<< 9))

def lengthEffect (s : RamState) : Effect :=
  { rip := 0x10f357
    writes := [⟨(.reg 13 : Operand 64), (.reg 13 : Operand 64).read s <<< 9⟩,
      ⟨(.reg 15 : Operand 64), lengthWord s⟩, ⟨(.mem (rspOf s + 136) : Operand 64), lengthWord s⟩,
      ⟨(.mem (rspOf s + 72) : Operand 64), lengthWord s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

structure LengthPre (s : RamState) : Prop where
  rip : s.RIP = 0x10f33c
  writable : ∀ o ∈ ([136,72] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 o) 8
  apart : ∀ o ∈ ([136,72] : List Nat), ∀ off len : Nat, off + len ≤ 27 →
    RangeApart (rspOf s + BitVec.ofNat 64 o) 8 (0x10f33c + BitVec.ofNat 64 off) len

attribute [local x86_local] StreamPadding.Stages.shift64_local StreamPadding.Stages.shift32_local
attribute [local x86_compose] shlR32Effect shlR64Effect encodeBswapR64

theorem storeLength [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pre : LengthPre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (lengthEffect s).Holds s t := by
  have code := programText_slice (programLoaded_codeIn loaded) 0xf33c lengthBytes
    (by decide) (by decide +kernel)
  suffices block : AdvanceTriple boundary LengthPre (codeRange 0x10f33c lengthBytes)
      (Effect.post lengthEffect) by
    obtain ⟨fuel,t,exec,rt,_,effect⟩ := block s ready code pre
    exact ⟨fuel,t,exec,rt,effect⟩
  advance_begin (StepEffect.forgetFlags (h := shl_r64_imm8_effect_step 0x10f33c
    0x49 0xe5 9 (by simp [RexWPrefix]) rfl rfl))
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xf340 (by decide))
  advance_then (StepEffect.forgetFlags (h := shl_r32_imm8_rex_effect_step 0x10f340
    0x41 0xe7 3 (by simp [RexNoWPrefix]) rfl rfl))
  case sub => exact codeRange_slice_subset 0x10f33c lengthBytes 4 4
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Effect.forgetFlags, shlR32Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf344 (by decide))
  advance_then (StepEffect.forgetFlags (h := or_r64_r64_effect_step 0x10f344
    0x4d 0xef (by simp [RexWPrefix]) rfl))
  case sub => exact codeRange_slice_subset 0x10f33c lengthBytes 8 3
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Effect.forgetFlags, orR64R64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf347 (by decide))
  advance_then (bswap_r64_effect_step 0x10f347 15)
  case sub => exact codeRange_slice_subset 0x10f33c lengthBytes 11 3
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [bswapR64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf34a (by decide))
  advance_then (mov_m64_r64_effect_step 0x10f34a 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f33c lengthBytes 14 8
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 136 (by decide)
    · x86_norm
      exact hp.apart 136 (by decide) 14 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 136 (by decide) 0 27 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf352 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10f352 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f33c lengthBytes 22 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 72 (by decide)
    · x86_norm
      exact hp.apart 72 (by decide) 22 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 72 (by decide) 0 27 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf357 (by decide))
  apply Field.AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [lengthEffect]
  · x86_norm [lengthEffect, lengthWord]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro flag; cases flag <;> x86_norm [lengthEffect]
  · x86_norm [lengthEffect]


end Hkdf.Proofs.NewExpand.Expand.Finalize
