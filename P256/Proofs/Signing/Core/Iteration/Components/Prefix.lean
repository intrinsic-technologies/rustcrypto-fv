import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Prefix

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

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10d19f
  byteWritable : MemWritable s (rspOf s+528) 1
  bitsWritable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (rspOf s+8) 4
  writable : ∀ i ∈ [1328,1336,1344,1352], MemWritable s (rspOf s+i) 8
  apart : ∀ off len : Nat, off+len ≤ 118431 →
    RangeApart (rspOf s+528) 1 (Extracted.textAddress + BitVec.ofNat 64 off) len
  bitsApart : ∀ off len : Nat, off+len ≤ 118431 →
    RangeApart (rspOf s+8) 4 (Extracted.textAddress + BitVec.ofNat 64 off) len
  wordsApart : ∀ i ∈ [1328,1336,1344,1352], ∀ off len : Nat, off+len ≤ 118431 →
    RangeApart (rspOf s+i) 8 (Extracted.textAddress + BitVec.ofNat 64 off) len

def bytes : List UInt8 :=
  [0xc6, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x1, 0xc6, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x0, 0xc6, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x0, 0xc6, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x0, 0xc7, 0x44, 0x24, 0x8, 0x0, 0x1, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x48, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x40, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x38, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x30, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbe, 0x20, 0x0, 0x0, 0x0, 0xb9, 0x4, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xfa, 0x41, 0xb8, 0x0, 0x1, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10d20d
    writes := [
      ⟨(.mem (rspOf s+528) : Operand 8), 0⟩,
      ⟨(.mem (rspOf s+8) : Operand 32), 256⟩,
      ⟨(.mem (rspOf s+1352) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+1344) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+1336) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+1328) : Operand 64), 0⟩,
      ⟨(.reg 6 : Operand 64), 32⟩,
      ⟨(.reg 1 : Operand 64), 4⟩,
      ⟨(.reg 7 : Operand 64), (.reg 13 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 15 : Operand 64).read s⟩,
      ⟨(.reg 8 : Operand 64), 256⟩] }

set_option maxHeartbeats 800000 in
theorem block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d19f bytes) (Effect.post effect) := by
  advance_begin (mov_m8_imm8_effect_step 0x10d19f (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl 1)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.byteWritable, hP.apart 0xd19f 8 (by decide)⟩
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd1a7 (by decide))
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.apart 0xd19f 110 (by decide)
  advance_then (mov_m8_imm8_effect_step 0x10d1a7 (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.byteWritable
    · x86_norm
      exact hP.apart 0xd1a7 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0xd19f 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd1af (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10d1af (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.byteWritable
    · x86_norm
      exact hP.apart 0xd1af 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0xd19f 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd1b7 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10d1b7 (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.byteWritable
    · x86_norm
      exact hP.apart 0xd1b7 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0xd19f 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd1bf (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m32_imm32_legacy_effect_step_any 0x10d1bf (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 256)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.bitsWritable
    · x86_norm
      exact hP.bitsApart 0xd1bf 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.bitsApart 0xd19f 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd1c7 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10d1c7 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1352)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 40 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1352 (by simp)
    · x86_norm
      exact hP.wordsApart 1352 (by simp) 0xd1c7 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 1352 (by simp) 0xd19f 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd1d3 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10d1d3 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1344)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 52 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1344 (by simp)
    · x86_norm
      exact hP.wordsApart 1344 (by simp) 0xd1d3 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 1344 (by simp) 0xd19f 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd1df (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10d1df 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1336)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 64 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1336 (by simp)
    · x86_norm
      exact hP.wordsApart 1336 (by simp) 0xd1df 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 1336 (by simp) 0xd19f 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd1eb (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10d1eb 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1328)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 76 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1328 (by simp)
    · x86_norm
      exact hP.wordsApart 1328 (by simp) 0xd1eb 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.wordsApart 1328 (by simp) 0xd19f 110 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd1f7 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10d1f7 0xbe (by decide) 32)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 88 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd1fc (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10d1fc 0xb9 (by decide) 4)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 93 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd201 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10d201 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 98 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd204 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10d204 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 101 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd207 (by decide))
  advance_then (mov_r32_imm32_rex_effect_step 0x10d207 0x41 0xb8 (by simp [RexNoWPrefix]) (by decide) 256)
  case sub => exact codeRange_slice_subset 0x10d19f bytes 104 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd20d (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s u _ h
  apply h.weaken
  · x86_norm [effect]
    all_goals try (repeat constructor <;> rfl)
    all_goals simp [gprNumber, rexR, modrmReg]
  · x86_norm [effect]
    all_goals try (repeat constructor <;> rfl)
    all_goals simp [gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [effect]
    all_goals try (repeat constructor <;> rfl)
  · x86_norm [effect]
    all_goals try (repeat constructor <;> rfl)

end P256.Proofs.Signing.Core.Iteration.Components.Prefix
