import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Scalar.Multiply

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x113063
  readable : ∀ k < 16, MemReadable s (rspOf s + BitVec.ofNat 64 (8*k)) 8
  writable : ∀ k < 8, MemWritable s (rspOf s + BitVec.ofNat 64 (8*k)) 8
  apart : ∀ k < 8, ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + BitVec.ofNat 64 (8*k)) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def copyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x44, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x8b, 0x4c, 0x24, 0x48, 0x48, 0x89, 0x4c, 0x24, 0x8, 0x48, 0x89, 0x4, 0x24, 0x48, 0x8b, 0x44, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x8b, 0x44, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x8b, 0x44, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8b, 0x44, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0xe6, 0x48, 0x8d, 0x54, 0x24, 0x20, 0x48, 0x89, 0xdf]

def copyEffect (s : RamState) : Effect :=
  { rip := 0x1130bd
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

macro "scalar_multiply_copy_block" hout:term:max : tactic =>
  `(tactic| (
  advance_begin (mov_r64_m64_effect_step 0x113063 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 11 (by decide)⟩
  case next =>
    intro _ _
    exact boundary_ne_program $hout (inProgram_of_textOffset 0x13068 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113068 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 3 (by decide)
    · x86_norm
      exact hP.apart 3 (by decide) 0x13068 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 3 (by decide) 0x13063 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1306d (by decide))
  advance_then (mov_r64_m64_effect_step 0x11306d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 10 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13072 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113072 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 2 (by decide)
    · x86_norm
      exact hP.apart 2 (by decide) 0x13072 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 2 (by decide) 0x13063 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13077 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113077 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1307c (by decide))
  advance_then (mov_r64_m64_effect_step 0x11307c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 9 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13081 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113081 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1 (by decide)
    · x86_norm
      exact hP.apart 1 (by decide) 0x13081 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1 (by decide) 0x13063 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13086 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113086 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 35 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.apart 0 (by decide) 0x13086 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0 (by decide) 0x13063 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1308a (by decide))
  advance_then (mov_r64_m64_effect_step 0x11308a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 39 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 15 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1308f (by decide))
  advance_then (mov_m64_r64_effect_step 0x11308f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 44 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 7 (by decide)
    · x86_norm
      exact hP.apart 7 (by decide) 0x1308f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 7 (by decide) 0x13063 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13094 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113094 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 49 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 14 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x13099 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113099 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 54 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 6 (by decide)
    · x86_norm
      exact hP.apart 6 (by decide) 0x13099 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 6 (by decide) 0x13063 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x1309e (by decide))
  advance_then (mov_r64_m64_effect_step 0x11309e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 59 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 13 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x130a3 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1130a3 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 64 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 5 (by decide)
    · x86_norm
      exact hP.apart 5 (by decide) 0x130a3 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 5 (by decide) 0x13063 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x130a8 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1130a8 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 69 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 12 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x130ad (by decide))
  advance_then (mov_m64_r64_effect_step 0x1130ad 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 74 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 4 (by decide)
    · x86_norm
      exact hP.apart 4 (by decide) 0x130ad 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 4 (by decide) 0x13063 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x130b2 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1130b2 0x48 0xe6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 79 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x130b5 (by decide))
  advance_then (lea_r64_effect_step 0x1130b5 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 82 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x130ba (by decide))
  advance_then (mov_r64_r64_effect_step 0x1130ba 0x48 0xdf (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x113063 copyBytes 87 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset 0x130bd (by decide))
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
    AdvanceTriple boundary (CopyPre) (codeRange 0x113063 copyBytes) (Effect.post (copyEffect)) := by
  scalar_multiply_copy_block hout

theorem copy_bytes_code :
    Extracted.textBytes.toListFrom 0x13063 copyBytes.length = copyBytes := by
  decide +kernel

end P256.Proofs.Scalar.Multiply
