import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Ecdh.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] movM8Imm8Effect

private theorem byteStoreLocal (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    Effect.Local (movM8Imm8Effect p am imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · intro s
    simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

attribute [local x86_local] byteStoreLocal

structure CopyYPre (s : RamState) : Prop where
  rip : s.RIP = 0x100447
  readable : ∀ i ∈ [48, 56, 64, 72], MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ [280, 288, 296, 304], MemWritable s (rspOf s + i) 8
  tagWritable : MemWritable s (rspOf s + 312) 1
  apart : ∀ i ∈ [280, 288, 296, 304], ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len
  tagApart : ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + 312) 1 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def copyYBytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x30,0x48,0x8b,0x4c,0x24,0x38,0x48,0x89,0x84,0x24,0x18,0x1,0x0,0x0,0x48,0x89,0x8c,0x24,0x20,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x40,0x48,0x89,0x84,0x24,0x28,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x48,0x48,0x89,0x84,0x24,0x30,0x1,0x0,0x0,0xc6,0x84,0x24,0x38,0x1,0x0,0x0,0x0]

def copyYEffect (s : RamState) : Effect :=
  { rip := 0x100483
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (rspOf s + 72) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 56) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 280) : Operand 64), (.mem (rspOf s + 48) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 288) : Operand 64), (.mem (rspOf s + 56) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 296) : Operand 64), (.mem (rspOf s + 64) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 304) : Operand 64), (.mem (rspOf s + 72) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 312) : Operand 8), 0⟩] }

set_option maxHeartbeats 800000 in
theorem copy_y_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyYPre (codeRange 0x100447 copyYBytes)
      (Effect.post copyYEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x100447 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 48 (by simp)⟩
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x44c (by decide))
  advance_then (mov_r64_m64_effect_step 0x10044c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100447 copyYBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 56 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x451 (by decide))
  advance_then (mov_m64_r64_effect_step 0x100451 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100447 copyYBytes 10 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 280 (by simp)
    · x86_norm
      exact hP.apart 280 (by simp) 0x451 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 280 (by simp) 0x447 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x459 (by decide))
  advance_then (mov_m64_r64_effect_step 0x100459 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100447 copyYBytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 288 (by simp)
    · x86_norm
      exact hP.apart 288 (by simp) 0x459 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 288 (by simp) 0x447 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x461 (by decide))
  advance_then (mov_r64_m64_effect_step 0x100461 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100447 copyYBytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 64 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x466 (by decide))
  advance_then (mov_m64_r64_effect_step 0x100466 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100447 copyYBytes 31 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 296 (by simp)
    · x86_norm
      exact hP.apart 296 (by simp) 0x466 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 296 (by simp) 0x447 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x46e (by decide))
  advance_then (mov_r64_m64_effect_step 0x10046e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100447 copyYBytes 39 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 72 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x473 (by decide))
  advance_then (mov_m64_r64_effect_step 0x100473 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100447 copyYBytes 44 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 304 (by simp)
    · x86_norm
      exact hP.apart 304 (by simp) 0x473 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 304 (by simp) 0x447 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x47b (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10047b (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x100447 copyYBytes 52 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.tagWritable
    · x86_norm
      exact hP.tagApart 0x47b 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.tagApart 0x447 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x483 (by decide))
  advance_finish [copyYEffect]

end P256.Proofs.Ecdh.Normalize.Finish
