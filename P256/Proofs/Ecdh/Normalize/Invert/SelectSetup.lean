import P256.Proofs.Ecdh.Normalize.Invert.Setup
import P256.Proofs.Common.Instructions.LegacyLoad
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.LegacyLoad (movR32M32LegacyEffect movR32M32LegacyEffect_components mov_r32_m32_legacy_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Ecdh.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] movR32M32LegacyEffect

structure SelectSetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x100355
  readable : MemReadable s (stackPtr s + 112) 4
  writable : ∀ k < 4, MemWritable s (stackPtr s + BitVec.ofNat 64 (16+8*k)) 8
  apart : ∀ k < 4, ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 (16+8*k)) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def selectSetupBytes : List UInt8 :=
  [72, 199, 68, 36, 40, 0, 0, 0, 0, 72, 199, 68, 36, 32, 0, 0, 0, 0, 72, 199, 68, 36, 24, 0, 0, 0, 0, 72, 199, 68, 36, 16, 0, 0, 0, 0, 139, 108, 36, 112, 76, 141, 180, 36, 88, 7, 0, 0, 72, 141, 116, 36, 16, 76, 137, 247, 76, 137, 250, 137, 233]

def selectSetupEffect (s : RamState) : Effect :=
  { rip := 0x100392
    writes := [
      ⟨(.mem (stackPtr s + 40) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), 0⟩,
      ⟨(.reg 5 : Operand 64), ((.mem (stackPtr s + 112) : Operand 32).read s).setWidth 64⟩,
      ⟨(.reg 14 : Operand 64), stackPtr s + 1880⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 16⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 1880⟩,
      ⟨(.reg 2 : Operand 64), (.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), ((.mem (stackPtr s + 112) : Operand 32).read s).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem select_setup_block [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SelectSetupPre (codeRange 0x100355 selectSetupBytes)
      (Effect.post selectSetupEffect) := by
  advance_begin (mov_m64_imm32_effect_step 0x100355 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable 3 (by decide), hP.apart 3 (by decide) 0x355 9 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.apart 3 (by decide) 0x355 61 (by decide)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x35e (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10035e 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x100355 selectSetupBytes 9 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 2 (by decide)
    · x86_norm
      exact hP.apart 2 (by decide) 0x35e 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 2 (by decide) 0x355 61 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x367 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x100367 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x100355 selectSetupBytes 18 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1 (by decide)
    · x86_norm
      exact hP.apart 1 (by decide) 0x367 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1 (by decide) 0x355 61 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x370 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x100370 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x100355 selectSetupBytes 27 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.apart 0 (by decide) 0x370 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0 (by decide) 0x355 61 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x379 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x100379 5 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100355 selectSetupBytes 36 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable
    · apply Effect.Avoids.of_noMem
      simp [movR32M32LegacyEffect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x37d (by decide))
  advance_then (lea_r64_effect_step 0x10037d 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 1880)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100355 selectSetupBytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x385 (by decide))
  advance_then (lea_r64_effect_step 0x100385 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100355 selectSetupBytes 48 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x38a (by decide))
  advance_then (mov_r64_r64_effect_step 0x10038a 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100355 selectSetupBytes 53 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x38d (by decide))
  advance_then (mov_r64_r64_effect_step 0x10038d 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100355 selectSetupBytes 56 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x390 (by decide))
  advance_then (mov_r32_r32_effect_step 0x100390 0xe9 rfl)
  case sub => exact codeRange_slice_subset 0x100355 selectSetupBytes 59 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x392 (by decide))
  advance_finish [selectSetupEffect, modrmReg, modrmRm, BitVec.add_zero,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

end P256.Proofs.Ecdh.Normalize
