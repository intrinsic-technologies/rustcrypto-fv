import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Field (AdvanceTriple)

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
  rip : s.RIP = 0x10df44
  readable : ∀ i ∈ [392, 400, 408, 416], MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ [608, 616, 624, 632], MemWritable s (rspOf s + i) 8
  tagWritable : MemWritable s (rspOf s + 640) 1
  apart : ∀ i ∈ [608, 616, 624, 632], ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len
  tagApart : ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + 640) 1 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def copyYBytes : List UInt8 :=
  [0x48,0x8b,0x84,0x24,0x88,0x1,0x0,0x0,0x48,0x8b,0x8c,0x24,0x90,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x60,0x2,0x0,0x0,0x48,0x89,0x8c,0x24,0x68,0x2,0x0,0x0,0x48,0x8b,0x84,0x24,0x98,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x70,0x2,0x0,0x0,0x48,0x8b,0x84,0x24,0xa0,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x78,0x2,0x0,0x0,0xc6,0x84,0x24,0x80,0x2,0x0,0x0,0x0]

def copyYEffect (s : RamState) : Effect :=
  { rip := 0x10df8c
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (rspOf s + 416) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 400) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 608) : Operand 64), (.mem (rspOf s + 392) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 616) : Operand 64), (.mem (rspOf s + 400) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 624) : Operand 64), (.mem (rspOf s + 408) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 632) : Operand 64), (.mem (rspOf s + 416) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 640) : Operand 8), 0⟩] }

set_option maxHeartbeats 800000 in
theorem copy_y_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyYPre (codeRange 0x10df44 copyYBytes)
      (Effect.post copyYEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10df44 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 392)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 392 (by simp)⟩
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0xdf4c (by decide))
  advance_then (mov_r64_m64_effect_step 0x10df4c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 400)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df44 copyYBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 400 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdf54 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10df54 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 608)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df44 copyYBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 608 (by simp)
    · x86_norm
      exact hP.apart 608 (by simp) 0xdf54 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 608 (by simp) 0xdf44 72 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdf5c (by decide))
  advance_then (mov_m64_r64_effect_step 0x10df5c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 616)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df44 copyYBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 616 (by simp)
    · x86_norm
      exact hP.apart 616 (by simp) 0xdf5c 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 616 (by simp) 0xdf44 72 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdf64 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10df64 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 408)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df44 copyYBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 408 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdf6c (by decide))
  advance_then (mov_m64_r64_effect_step 0x10df6c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 624)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df44 copyYBytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 624 (by simp)
    · x86_norm
      exact hP.apart 624 (by simp) 0xdf6c 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 624 (by simp) 0xdf44 72 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdf74 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10df74 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 416)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df44 copyYBytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 416 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdf7c (by decide))
  advance_then (mov_m64_r64_effect_step 0x10df7c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 632)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10df44 copyYBytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 632 (by simp)
    · x86_norm
      exact hP.apart 632 (by simp) 0xdf7c 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 632 (by simp) 0xdf44 72 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdf84 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10df84 (.sib 4 none 0 (.d32 640)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10df44 copyYBytes 64 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.tagWritable
    · x86_norm
      exact hP.tagApart 0xdf84 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.tagApart 0xdf44 72 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xdf8c (by decide))
  advance_finish [copyYEffect]

end P256.Proofs.Verifying.Core.Finish
