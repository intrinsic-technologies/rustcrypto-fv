import P256.Proofs.Verifying.Core.Normalize.InverseSetup
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Normalize.CopyY

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Field (AdvanceTriple)

structure CopyPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  readable : ∀ k < 4, MemReadable s
    (stackPtr s + ((32#8) + BitVec.ofNat 8 (8*k)).signExtend 64) 8
  writable : ∀ k < 4, MemWritable s (stackPtr s + BitVec.ofNat 64 (128 + 8*k)) 8
  apart : ∀ k < 4, ∀ offset len : Nat, offset + len ≤ 52 →
    RangeApart (stackPtr s + BitVec.ofNat 64 (128 + 8*k)) 8 (p + BitVec.ofNat 64 offset) len

def copyBytes : List UInt8 :=
  encodeMovR64M64 0 (.sib 4 none 0 (.d8 ((32#8) + 24))) ++
    encodeMovM64R64 0 (.sib 4 none 0 (.d32 152)) ++
    encodeMovR64M64 0 (.sib 4 none 0 (.d8 ((32#8) + 16))) ++
    encodeMovM64R64 0 (.sib 4 none 0 (.d32 144)) ++
    encodeMovR64M64 0 (.sib 4 none 0 (.d8 ((32#8) + 0))) ++
    encodeMovR64M64 1 (.sib 4 none 0 (.d8 ((32#8) + 8))) ++
    encodeMovM64R64 1 (.sib 4 none 0 (.d32 136)) ++
    encodeMovM64R64 0 (.sib 4 none 0 (.d32 128))

theorem copyBytes_length : copyBytes.length = 52 := by
  rfl

def copyEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 52
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + (32#8).signExtend 64) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + ((32#8) + 8).signExtend 64) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 128) : Operand 64), (.mem (stackPtr s + (32#8).signExtend 64) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 136) : Operand 64), (.mem (stackPtr s + ((32#8) + 8).signExtend 64) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 144) : Operand 64), (.mem (stackPtr s + ((32#8) + 16).signExtend 64) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 152) : Operand 64), (.mem (stackPtr s + ((32#8) + 24).signExtend 64) : Operand 64).read s⟩] }

set_option maxHeartbeats 800000 in
theorem copy_block [Bindings] (p : BitVec 64)
    (boundary : ReturnBoundary)
    (hout : ∀ i ≤ 52, p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (CopyPre p) (codeRange p copyBytes)
      (Effect.post (copyEffect p)) := by
  let value := (32#8)
  advance_begin (mov_r64_m64_effect_step p 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 (value + 24))) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 3 (by decide)⟩
  case next =>
    intro _ _
    exact hout 5 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 5) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p copyBytes 5 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 3 (by decide)
    · x86_norm
      exact hP.apart 3 (by decide) 5 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have hh := hP.apart 3 (by decide) 0 52 (by decide)
      simp only [BitVec.add_zero] at hh
      exact hh
    · x86_norm
      exact hout 13 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 13) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 (value + 16))) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p copyBytes 13 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 2 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact hout 18 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 18) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p copyBytes 18 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 2 (by decide)
    · x86_norm
      exact hP.apart 2 (by decide) 18 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have hh := hP.apart 2 (by decide) 0 52 (by decide)
      simp only [BitVec.add_zero] at hh
      exact hh
    · x86_norm
      exact hout 26 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 26) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 (value + 0))) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p copyBytes 26 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 0 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact hout 31 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 31) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 (value + 8))) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p copyBytes 31 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact hout 36 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 36) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p copyBytes 36 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1 (by decide)
    · x86_norm
      exact hP.apart 1 (by decide) 36 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have hh := hP.apart 1 (by decide) 0 52 (by decide)
      simp only [BitVec.add_zero] at hh
      exact hh
    · x86_norm
      exact hout 44 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 44) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p copyBytes 44 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.apart 0 (by decide) 44 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have hh := hP.apart 0 (by decide) 0 52 (by decide)
      simp only [BitVec.add_zero] at hh
      exact hh
    · x86_norm
      exact hout 52 (by decide)
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [copyEffect, value]
  · x86_norm [copyEffect, value]
    repeat constructor <;> rfl
  · intro i
    cases i <;> x86_norm [copyEffect, value]
  · x86_norm [copyEffect, value]
end P256.Proofs.Verifying.Core.Normalize.CopyY
