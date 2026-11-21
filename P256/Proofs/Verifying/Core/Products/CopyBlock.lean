import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Core.Products

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x113343
  readable : ∀ k < 16, MemReadable s (rspOf s + BitVec.ofNat 64 (8*k)) 8
  writable : ∀ k < 8, MemWritable s (rspOf s + BitVec.ofNat 64 (8*k)) 8
  apart : ∀ k < 8, ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + BitVec.ofNat 64 (8*k)) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def copyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x44, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x8b, 0x4c, 0x24, 0x48, 0x48, 0x89, 0x4c, 0x24, 0x8, 0x48, 0x89, 0x4, 0x24, 0x48, 0x8b, 0x44, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x8b, 0x44, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x8b, 0x44, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8b, 0x44, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0xe6, 0x48, 0x8d, 0x54, 0x24, 0x20, 0x48, 0x89, 0xdf]

def copyEffect (s : RamState) : Effect :=
  { rip := 0x11339d
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (rspOf s + 96) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 72) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), rspOf s + 32⟩,
      ⟨(.reg 6 : Operand 64), rspOf s⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 0) : Operand 64), (.mem (rspOf s + 64) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 8) : Operand 64), (.mem (rspOf s + 72) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), (.mem (rspOf s + 80) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 24) : Operand 64), (.mem (rspOf s + 88) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 32) : Operand 64), (.mem (rspOf s + 96) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 40) : Operand 64), (.mem (rspOf s + 104) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 48) : Operand 64), (.mem (rspOf s + 112) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 56) : Operand 64), (.mem (rspOf s + 120) : Operand 64).read s⟩] }

macro "verifying_products_copy_block" hout:term:max : tactic =>
  `(tactic| (
  advance_begin (mov_r64_m64_effect_step 0x113343 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 11 (by decide)⟩
  case next =>
    intro _ _
    exact boundary_ne_program $hout (inProgram_of_textOffset 0x13348 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113348 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 3 (by decide)
    · x86_norm
      exact hP.apart 3 (by decide) 0x13348 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 3 (by decide) 0x13343 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1334d (by decide))
  advance_then (mov_r64_m64_effect_step 0x11334d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 10 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13352 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113352 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 2 (by decide)
    · x86_norm
      exact hP.apart 2 (by decide) 0x13352 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 2 (by decide) 0x13343 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13357 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113357 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1335c (by decide))
  advance_then (mov_r64_m64_effect_step 0x11335c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 9 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13361 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113361 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1 (by decide)
    · x86_norm
      exact hP.apart 1 (by decide) 0x13361 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1 (by decide) 0x13343 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13366 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113366 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 35 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.apart 0 (by decide) 0x13366 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0 (by decide) 0x13343 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1336a (by decide))
  advance_then (mov_r64_m64_effect_step 0x11336a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 39 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 15 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1336f (by decide))
  advance_then (mov_m64_r64_effect_step 0x11336f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 44 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 7 (by decide)
    · x86_norm
      exact hP.apart 7 (by decide) 0x1336f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 7 (by decide) 0x13343 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13374 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113374 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 49 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 14 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13379 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113379 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 54 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 6 (by decide)
    · x86_norm
      exact hP.apart 6 (by decide) 0x13379 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 6 (by decide) 0x13343 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1337e (by decide))
  advance_then (mov_r64_m64_effect_step 0x11337e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 59 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 13 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13383 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113383 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 64 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 5 (by decide)
    · x86_norm
      exact hP.apart 5 (by decide) 0x13383 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 5 (by decide) 0x13343 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13388 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113388 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 69 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 12 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1338d (by decide))
  advance_then (mov_m64_r64_effect_step 0x11338d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 74 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 4 (by decide)
    · x86_norm
      exact hP.apart 4 (by decide) 0x1338d 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 4 (by decide) 0x13343 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13392 (by decide))
  advance_then (mov_r64_r64_effect_step 0x113392 0x48 0xe6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 79 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13395 (by decide))
  advance_then (lea_r64_effect_step 0x113395 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 82 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1339a (by decide))
  advance_then (mov_r64_r64_effect_step 0x11339a 0x48 0xdf (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x113343 copyBytes 87 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1339d (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [copyEffect]
  · x86_norm [copyEffect]
    repeat constructor <;> rfl
  · intro i
    cases i <;> x86_norm [copyEffect]
  · x86_norm [copyEffect]
  ))

set_option maxHeartbeats 1200000 in
theorem copy_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (CopyPre) (codeRange 0x113343 copyBytes) (Effect.post (copyEffect)) := by
  verifying_products_copy_block hout

theorem copy_bytes_code :
    Extracted.textBytes.toListFrom 0x13343 copyBytes.length = copyBytes := by
  decide +kernel

end P256.Proofs.Verifying.Core.Products
