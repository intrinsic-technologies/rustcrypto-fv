import P256.Proofs.Verifying.Core.Digest.Setup.Initialize
import P256.Proofs.Verifying.Core.Digest.Setup.Prefix

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail.Setup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

attribute [local x86_compose] movM8Imm8Effect

private theorem byteStoreLocal (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    Effect.Local (movM8Imm8Effect p am imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · intro s
    simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

attribute [local x86_local] byteStoreLocal

structure SetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x10e098
  byteWritable : MemWritable s (rspOf s+128) 1
  bitsWritable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (rspOf s+576) 4
  writable : ∀ i ∈ [0,8,16,24], MemWritable s (rspOf s+i) 8
  apart : ∀ off len : Nat, off+len ≤ 118431 →
    RangeApart (rspOf s+128) 1 (Extracted.textAddress + BitVec.ofNat 64 off) len
  bitsApart : ∀ off len : Nat, off+len ≤ 118431 →
    RangeApart (rspOf s+576) 4 (Extracted.textAddress + BitVec.ofNat 64 off) len
  wordsApart : ∀ i ∈ [0,8,16,24], ∀ off len : Nat, off+len ≤ 118431 →
    RangeApart (rspOf s+i) 8 (Extracted.textAddress + BitVec.ofNat 64 off) len

def setupBytes : List UInt8 :=
  [0xc6,0x84,0x24,0x80,0x0,0x0,0x0,0x1,0x48,0x8d,0x84,0x24,0x80,0x0,0x0,0x0,0xc6,0x84,0x24,0x80,0x0,0x0,0x0,0x0,0xc6,0x84,0x24,0x80,0x0,0x0,0x0,0x0,0xc6,0x84,0x24,0x80,0x0,0x0,0x0,0x0,0xc7,0x84,0x24,0x40,0x2,0x0,0x0,0x0,0x1,0x0,0x0,0x48,0xc7,0x44,0x24,0x18,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x10,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x8,0x0,0x0,0x0,0x0,0x48,0xc7,0x4,0x24,0x0,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0x88,0x1,0x0,0x0,0x48,0x89,0xe2,0xbe,0x20,0x0,0x0,0x0,0xb9,0x4,0x0,0x0,0x0,0x41,0xb8,0x0,0x1,0x0,0x0]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10e109
    writes := [
      ⟨(.reg 0 : Operand 64), rspOf s+128⟩,
      ⟨(.mem (rspOf s+128) : Operand 8), 0⟩,
      ⟨(.mem (rspOf s+576) : Operand 32), 256⟩,
      ⟨(.mem (rspOf s+24) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+16) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+8) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+0) : Operand 64), 0⟩,
      ⟨(.reg 7 : Operand 64), rspOf s+392⟩,
      ⟨(.reg 2 : Operand 64), rspOf s+0⟩,
      ⟨(.reg 6 : Operand 64), 32⟩,
      ⟨(.reg 1 : Operand 64), 4⟩,
      ⟨(.reg 8 : Operand 64), 256⟩] }

set_option maxHeartbeats 800000 in
theorem setup_block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SetupPre (codeRange 0x10e098 setupBytes) (Effect.post setupEffect) := by
  advance_begin (mov_m8_imm8_effect_step 0x10e098 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl 1)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.byteWritable, hP.apart 0xe098 8 (by decide)⟩
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0xe0a0 (by decide))
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.apart 0xe098 113 (by decide)
  advance_then (lea_r64_effect_step 0x10e0a0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0a8 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10e0a8 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.byteWritable
    · x86_norm
      exact hP.apart 0xe0a8 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0xe098 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0b0 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10e0b0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.byteWritable
    · x86_norm
      exact hP.apart 0xe0b0 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0xe098 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0b8 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10e0b8 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.byteWritable
    · x86_norm
      exact hP.apart 0xe0b8 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0xe098 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0c0 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m32_imm32_legacy_effect_step_any 0x10e0c0 (.sib 4 none 0 (.d32 576)) (by decide +kernel) rfl rfl 256)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 40 11
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.bitsWritable
    · x86_norm
      exact hP.bitsApart 0xe0c0 11 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.bitsApart 0xe098 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0cb (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10e0cb 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 51 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.wordsApart 24 (by simp) 0xe0cb 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 24 (by simp) 0xe098 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0d4 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10e0d4 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 60 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.wordsApart 16 (by simp) 0xe0d4 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 16 (by simp) 0xe098 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0dd (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10e0dd 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 69 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.wordsApart 8 (by simp) 0xe0dd 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 8 (by simp) 0xe098 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0e6 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10e0e6 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 .none) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 78 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.wordsApart 0 (by simp) 0xe0e6 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 0 (by simp) 0xe098 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0ee (by decide))
  advance_then (lea_r64_effect_step 0x10e0ee 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 392)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 86 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0f6 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10e0f6 0x48 0xe2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 94 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0f9 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10e0f9 0xbe (by decide) 32)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 97 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe0fe (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10e0fe 0xb9 (by decide) 4)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 102 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe103 (by decide))
  advance_then (mov_r32_imm32_rex_effect_step 0x10e103 0x41 0xb8 (by simp [RexNoWPrefix]) (by decide) 256)
  case sub => exact codeRange_slice_subset 0x10e098 setupBytes 107 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe109 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [setupEffect]
  · x86_norm [setupEffect, BitVec.add_zero]
    right; right; right; right; right
    rfl
  · intro i
    cases i <;> x86_norm [setupEffect]
  · x86_norm [setupEffect]

end P256.Proofs.Verifying.Core.Finish.Tail.Setup
