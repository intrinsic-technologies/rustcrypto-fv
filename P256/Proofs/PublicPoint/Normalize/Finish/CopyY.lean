import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.PublicPoint.Normalize.Finish

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
  rip : s.RIP = 0x10ea45
  readable : ∀ i ∈ [32, 40, 48, 56], MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ [1064, 1072, 1080, 1088], MemWritable s (rspOf s + i) 8
  tagWritable : MemWritable s (rspOf s + 1096) 1
  apart : ∀ i ∈ [1064, 1072, 1080, 1088], ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len
  tagApart : ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + 1096) 1 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def copyYBytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x20,0x48,0x8b,0x4c,0x24,0x28,0x48,0x89,0x84,0x24,0x28,0x4,0x0,0x0,0x48,0x89,0x8c,0x24,0x30,0x4,0x0,0x0,0x48,0x8b,0x44,0x24,0x30,0x48,0x89,0x84,0x24,0x38,0x4,0x0,0x0,0x48,0x8b,0x44,0x24,0x38,0x48,0x89,0x84,0x24,0x40,0x4,0x0,0x0,0xc6,0x84,0x24,0x48,0x4,0x0,0x0,0x0]

def copyYEffect (s : RamState) : Effect :=
  { rip := 0x10ea81
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (rspOf s + 56) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 40) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 1064) : Operand 64), (.mem (rspOf s + 32) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 1072) : Operand 64), (.mem (rspOf s + 40) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 1080) : Operand 64), (.mem (rspOf s + 48) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 1088) : Operand 64), (.mem (rspOf s + 56) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 1096) : Operand 8), 0⟩] }

set_option maxHeartbeats 800000 in
theorem copy_y_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyYPre (codeRange 0x10ea45 copyYBytes)
      (Effect.post copyYEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10ea45 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 32 (by simp)⟩
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0xea4a (by decide))
  advance_then (mov_r64_m64_effect_step 0x10ea4a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ea45 copyYBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 40 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xea4f (by decide))
  advance_then (mov_m64_r64_effect_step 0x10ea4f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1064)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ea45 copyYBytes 10 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1064 (by simp)
    · x86_norm
      exact hP.apart 1064 (by simp) 0xea4f 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1064 (by simp) 0xea45 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xea57 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10ea57 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 1072)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ea45 copyYBytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1072 (by simp)
    · x86_norm
      exact hP.apart 1072 (by simp) 0xea57 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1072 (by simp) 0xea45 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xea5f (by decide))
  advance_then (mov_r64_m64_effect_step 0x10ea5f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ea45 copyYBytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 48 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xea64 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10ea64 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1080)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ea45 copyYBytes 31 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1080 (by simp)
    · x86_norm
      exact hP.apart 1080 (by simp) 0xea64 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1080 (by simp) 0xea45 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xea6c (by decide))
  advance_then (mov_r64_m64_effect_step 0x10ea6c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ea45 copyYBytes 39 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 56 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xea71 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10ea71 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1088)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ea45 copyYBytes 44 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1088 (by simp)
    · x86_norm
      exact hP.apart 1088 (by simp) 0xea71 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1088 (by simp) 0xea45 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xea79 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10ea79 (.sib 4 none 0 (.d32 1096)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10ea45 copyYBytes 52 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.tagWritable
    · x86_norm
      exact hP.tagApart 0xea79 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.tagApart 0xea45 60 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xea81 (by decide))
  advance_finish [copyYEffect]

end P256.Proofs.PublicPoint.Normalize.Finish
