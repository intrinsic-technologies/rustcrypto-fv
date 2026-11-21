import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Montgomery.Wrapper

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CopyPre (square : Bool) (s : RamState) : Prop where
  rip : s.RIP = (if square then 0x113823 else 0x1138b3)
  readable : ∀ k < 16, MemReadable s (rspOf s + BitVec.ofNat 64 (8*k)) 8
  writable : ∀ k < 8, MemWritable s (rspOf s + BitVec.ofNat 64 (8*k)) 8
  apart : ∀ k < 8, ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + BitVec.ofNat 64 (8*k)) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def copyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x44, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x8b, 0x4c, 0x24, 0x48, 0x48, 0x89, 0x4c, 0x24, 0x8, 0x48, 0x89, 0x4, 0x24, 0x48, 0x8b, 0x44, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x8b, 0x44, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x8b, 0x44, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8b, 0x44, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0xe6, 0x48, 0x8d, 0x54, 0x24, 0x20, 0x48, 0x89, 0xdf]

def copyEffect (square : Bool) (s : RamState) : Effect :=
  { rip := (if square then 0x11387d else 0x11390d)
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

macro "montgomery_copy_block_proof" square:term:max hout:term:max : tactic =>
  `(tactic| (
  advance_begin (mov_r64_m64_effect_step (if $square then 0x113823 else 0x1138b3) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 11 (by decide)⟩
  case next =>
    intro _ _
    exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x13828 else 0x138b8) (by decide))
  advance_then (mov_m64_r64_effect_step (if $square then 0x113828 else 0x1138b8) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 3 (by decide)
    · x86_norm
      exact hP.apart 3 (by decide) (if $square then 0x13828 else 0x138b8) 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 3 (by decide) (if $square then 0x13823 else 0x138b3) 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x1382d else 0x138bd) (by decide))
  advance_then (mov_r64_m64_effect_step (if $square then 0x11382d else 0x1138bd) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 10 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x13832 else 0x138c2) (by decide))
  advance_then (mov_m64_r64_effect_step (if $square then 0x113832 else 0x1138c2) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 2 (by decide)
    · x86_norm
      exact hP.apart 2 (by decide) (if $square then 0x13832 else 0x138c2) 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 2 (by decide) (if $square then 0x13823 else 0x138b3) 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x13837 else 0x138c7) (by decide))
  advance_then (mov_r64_m64_effect_step (if $square then 0x113837 else 0x1138c7) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x1383c else 0x138cc) (by decide))
  advance_then (mov_r64_m64_effect_step (if $square then 0x11383c else 0x1138cc) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 9 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x13841 else 0x138d1) (by decide))
  advance_then (mov_m64_r64_effect_step (if $square then 0x113841 else 0x1138d1) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1 (by decide)
    · x86_norm
      exact hP.apart 1 (by decide) (if $square then 0x13841 else 0x138d1) 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1 (by decide) (if $square then 0x13823 else 0x138b3) 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x13846 else 0x138d6) (by decide))
  advance_then (mov_m64_r64_effect_step (if $square then 0x113846 else 0x1138d6) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 35 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.apart 0 (by decide) (if $square then 0x13846 else 0x138d6) 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0 (by decide) (if $square then 0x13823 else 0x138b3) 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x1384a else 0x138da) (by decide))
  advance_then (mov_r64_m64_effect_step (if $square then 0x11384a else 0x1138da) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 39 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 15 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x1384f else 0x138df) (by decide))
  advance_then (mov_m64_r64_effect_step (if $square then 0x11384f else 0x1138df) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 44 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 7 (by decide)
    · x86_norm
      exact hP.apart 7 (by decide) (if $square then 0x1384f else 0x138df) 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 7 (by decide) (if $square then 0x13823 else 0x138b3) 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x13854 else 0x138e4) (by decide))
  advance_then (mov_r64_m64_effect_step (if $square then 0x113854 else 0x1138e4) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 49 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 14 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x13859 else 0x138e9) (by decide))
  advance_then (mov_m64_r64_effect_step (if $square then 0x113859 else 0x1138e9) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 54 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 6 (by decide)
    · x86_norm
      exact hP.apart 6 (by decide) (if $square then 0x13859 else 0x138e9) 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 6 (by decide) (if $square then 0x13823 else 0x138b3) 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x1385e else 0x138ee) (by decide))
  advance_then (mov_r64_m64_effect_step (if $square then 0x11385e else 0x1138ee) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 59 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 13 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x13863 else 0x138f3) (by decide))
  advance_then (mov_m64_r64_effect_step (if $square then 0x113863 else 0x1138f3) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 64 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 5 (by decide)
    · x86_norm
      exact hP.apart 5 (by decide) (if $square then 0x13863 else 0x138f3) 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 5 (by decide) (if $square then 0x13823 else 0x138b3) 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x13868 else 0x138f8) (by decide))
  advance_then (mov_r64_m64_effect_step (if $square then 0x113868 else 0x1138f8) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 69 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 12 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x1386d else 0x138fd) (by decide))
  advance_then (mov_m64_r64_effect_step (if $square then 0x11386d else 0x1138fd) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 74 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 4 (by decide)
    · x86_norm
      exact hP.apart 4 (by decide) (if $square then 0x1386d else 0x138fd) 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 4 (by decide) (if $square then 0x13823 else 0x138b3) 90 (by decide)
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x13872 else 0x13902) (by decide))
  advance_then (mov_r64_r64_effect_step (if $square then 0x113872 else 0x113902) 0x48 0xe6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 79 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x13875 else 0x13905) (by decide))
  advance_then (lea_r64_effect_step (if $square then 0x113875 else 0x113905) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 82 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x1387a else 0x1390a) (by decide))
  advance_then (mov_r64_r64_effect_step (if $square then 0x11387a else 0x11390a) 0x48 0xdf (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset (if $square then 0x113823 else 0x1138b3) copyBytes 87 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset (if $square then 0x1387d else 0x1390d) (by decide))
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
theorem copy_block [Bindings] (square : Bool) (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (CopyPre square) (codeRange (if square then 0x113823 else 0x1138b3) copyBytes) (Effect.post (copyEffect square)) := by
  cases square
  · montgomery_copy_block_proof false hout
  · montgomery_copy_block_proof true hout

theorem copy_bytes_code (square : Bool) :
    Extracted.textBytes.toListFrom (if square then 0x13823 else 0x138b3) copyBytes.length = copyBytes := by
  cases square <;> decide +kernel

end P256.Proofs.Field.Montgomery.Wrapper
