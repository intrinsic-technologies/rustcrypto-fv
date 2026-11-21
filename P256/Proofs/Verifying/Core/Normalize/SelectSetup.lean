import P256.Proofs.Verifying.Core.Normalize.InverseSetup
import P256.Proofs.Common.Instructions.LegacyLoad
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.LegacyLoad
  (movR32M32LegacyEffect movR32M32LegacyEffect_components mov_r32_m32_legacy_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Core.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] movR32M32LegacyEffect

structure SelectSetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x10de56
  readable : MemReadable s (stackPtr s + 928) 4
  writable : ∀ k < 4, MemWritable s (stackPtr s + BitVec.ofNat 64 (864+8*k)) 8
  apart : ∀ k < 4, ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 (864+8*k)) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def selectSetupBytes : List UInt8 :=
  [0x48,0xc7,0x84,0x24,0x78,0x3,0x0,0x0,0x0,0x0,0x0,0x0,0x48,0xc7,0x84,0x24,0x70,0x3,0x0,0x0,0x0,0x0,0x0,0x0,0x48,0xc7,0x84,0x24,0x68,0x3,0x0,0x0,0x0,0x0,0x0,0x0,0x48,0xc7,0x84,0x24,0x60,0x3,0x0,0x0,0x0,0x0,0x0,0x0,0x8b,0x9c,0x24,0xa0,0x3,0x0,0x0,0x4c,0x8d,0xb4,0x24,0x48,0x4,0x0,0x0,0x48,0x8d,0xb4,0x24,0x60,0x3,0x0,0x0,0x4c,0x89,0xf7,0x4c,0x89,0xfa,0x89,0xd9]

def selectSetupEffect (s : RamState) : Effect :=
  { rip := 0x10dea5
    writes := [
      ⟨(.mem (stackPtr s + 888) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 880) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 872) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 864) : Operand 64), 0⟩,
      ⟨(.reg 3 : Operand 64), ((.mem (stackPtr s + 928) : Operand 32).read s).setWidth 64⟩,
      ⟨(.reg 14 : Operand 64), stackPtr s + 1096⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 864⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 1096⟩,
      ⟨(.reg 2 : Operand 64), (.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), ((.mem (stackPtr s + 928) : Operand 32).read s).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem select_setup_block [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SelectSetupPre (codeRange 0x10de56 selectSetupBytes)
      (Effect.post selectSetupEffect) := by
  advance_begin (mov_m64_imm32_effect_step 0x10de56 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 888)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable 3 (by decide), hP.apart 3 (by decide) 0xde56 12 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.apart 3 (by decide) 0xde56 79 (by decide)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0xde62 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10de62 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 880)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10de56 selectSetupBytes 12 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 2 (by decide)
    · x86_norm
      exact hP.apart 2 (by decide) 0xde62 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 2 (by decide) 0xde56 79 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xde6e (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10de6e 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 872)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10de56 selectSetupBytes 24 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1 (by decide)
    · x86_norm
      exact hP.apart 1 (by decide) 0xde6e 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1 (by decide) 0xde56 79 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xde7a (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10de7a 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 864)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10de56 selectSetupBytes 36 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.apart 0 (by decide) 0xde7a 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0 (by decide) 0xde56 79 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xde86 (by decide))
  advance_then (mov_r32_m32_legacy_effect_step 0x10de86 3 (.sib 4 none 0 (.d32 928)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10de56 selectSetupBytes 48 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable
    · apply Effect.Avoids.of_noMem
      simp [movR32M32LegacyEffect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xde8d (by decide))
  advance_then (lea_r64_effect_step 0x10de8d 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 1096)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10de56 selectSetupBytes 55 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xde95 (by decide))
  advance_then (lea_r64_effect_step 0x10de95 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 864)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10de56 selectSetupBytes 63 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xde9d (by decide))
  advance_then (mov_r64_r64_effect_step 0x10de9d 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10de56 selectSetupBytes 71 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdea0 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10dea0 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10de56 selectSetupBytes 74 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdea3 (by decide))
  advance_then (mov_r32_r32_effect_step 0x10dea3 0xd9 rfl)
  case sub => exact codeRange_slice_subset 0x10de56 selectSetupBytes 77 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdea5 (by decide))
  advance_finish [selectSetupEffect,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

end P256.Proofs.Verifying.Core.Normalize
