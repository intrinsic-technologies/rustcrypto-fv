import P256.Proofs.PublicPoint.Normalize.Invert.Setup
import P256.Proofs.Common.Instructions.LegacyLoad
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.LegacyLoad (movR32M32LegacyEffect movR32M32LegacyEffect_components mov_r32_m32_legacy_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.PublicPoint.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] movR32M32LegacyEffect

structure SelectSetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x10e96b
  readable : MemReadable s (stackPtr s + 192) 4
  writable : ∀ k < 4, MemWritable s (stackPtr s + BitVec.ofNat 64 (8*k)) 8
  apart : ∀ k < 4, ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 (8*k)) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def selectSetupBytes : List UInt8 :=
  [72, 199, 68, 36, 24, 0, 0, 0, 0, 72, 199, 68, 36, 16, 0, 0, 0, 0, 72, 199, 68, 36, 8, 0, 0, 0, 0, 72, 199, 4, 36, 0, 0, 0, 0, 139, 172, 36, 192, 0, 0, 0, 76, 141, 180, 36, 232, 0, 0, 0, 72, 137, 230, 76, 137, 247, 76, 137, 250, 137, 233]

def selectSetupEffect (s : RamState) : Effect :=
  { rip := 0x10e9a8
    writes := [
      ⟨(.mem (stackPtr s + 24) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 0) : Operand 64), 0⟩,
      ⟨(.reg 5 : Operand 64), ((.mem (stackPtr s + 192) : Operand 32).read s).setWidth 64⟩,
      ⟨(.reg 14 : Operand 64), stackPtr s + 232⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 0⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 232⟩,
      ⟨(.reg 2 : Operand 64), (.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), ((.mem (stackPtr s + 192) : Operand 32).read s).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem select_setup_block [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SelectSetupPre (codeRange 0x10e96b selectSetupBytes)
      (Effect.post selectSetupEffect) := by
  advance_begin (mov_m64_imm32_effect_step 0x10e96b 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable 3 (by decide), hP.apart 3 (by decide) 0xe96b 9 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.apart 3 (by decide) 0xe96b 61 (by decide)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0xe974 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10e974 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10e96b selectSetupBytes 9 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 2 (by decide)
    · x86_norm
      exact hP.apart 2 (by decide) 0xe974 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 2 (by decide) 0xe96b 61 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xe97d (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10e97d 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10e96b selectSetupBytes 18 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1 (by decide)
    · x86_norm
      exact hP.apart 1 (by decide) 0xe97d 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1 (by decide) 0xe96b 61 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xe986 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10e986 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.none)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10e96b selectSetupBytes 27 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.apart 0 (by decide) 0xe986 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0 (by decide) 0xe96b 61 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xe98e (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x10e98e 5 (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e96b selectSetupBytes 35 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable
    · apply Effect.Avoids.of_noMem
      simp [movR32M32LegacyEffect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xe995 (by decide))
  advance_then (lea_r64_effect_step 0x10e995 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 232)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e96b selectSetupBytes 42 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xe99d (by decide))
  advance_then (mov_r64_r64_effect_step 0x10e99d 0x48 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e96b selectSetupBytes 50 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xe9a0 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10e9a0 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e96b selectSetupBytes 53 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xe9a3 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10e9a3 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e96b selectSetupBytes 56 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xe9a6 (by decide))
  advance_then (mov_r32_r32_effect_step 0x10e9a6 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x10e96b selectSetupBytes 59 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xe9a8 (by decide))
  advance_finish [selectSetupEffect, modrmReg, modrmRm, BitVec.add_zero,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

end P256.Proofs.PublicPoint.Normalize
