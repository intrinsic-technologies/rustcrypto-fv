import P256.Proofs.Verifying.Combination.Entry
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)

structure PointerPre (entry : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = entry
  writable : ∀ k < 6, MemWritable s ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 (32 + 8*k)) 8
  apart : ∀ k < 6, ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 (32 + 8*k)) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def tablePointerBytes : List UInt8 :=
  [0x48, 0x8d, 0x84, 0x24, 0x38, 0x5, 0x0, 0x0, 0x48, 0x89, 0x5c, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x8d, 0x44, 0x24, 0x7, 0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x8d, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8d, 0xac, 0x24, 0x68, 0x7, 0x0, 0x0, 0x4c, 0x8d, 0x7c, 0x24, 0x20, 0x48, 0x89, 0xef, 0x4c, 0x89, 0xfe]

def pointerEffect (ip : BitVec 64) (r : BitVec 5) (s : RamState) : Effect :=
  { rip := ip
    writes := [⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 56) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 72) : Operand 64), (Operand.reg 4 : Operand 64).read s + 1336⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 64) : Operand 64), (Operand.reg 4 : Operand 64).read s + 7⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), (Operand.reg 4 : Operand 64).read s + 56⟩,
      ⟨(Operand.reg 0 : Operand 64), (Operand.reg 4 : Operand 64).read s + 56⟩,
      ⟨(Operand.reg r : Operand 64), (Operand.reg 4 : Operand 64).read s + 1896⟩,
      ⟨(Operand.reg 15 : Operand 64), (Operand.reg 4 : Operand 64).read s + 32⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 32⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1896⟩] }

def tablePointerEffect : RamState → Effect := pointerEffect 0x10657d 5

set_option maxHeartbeats 800000 in
theorem tablePointer_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (PointerPre 0x106544) (codeRange 0x106544 tablePointerBytes)
      (Effect.post tablePointerEffect) := by
  advance_begin (lea_r64_effect_step 0x106544 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1336)) (by decide +kernel) rfl rfl)
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x654c (by decide))
  advance_then (mov_m64_r64_effect_step 0x10654c 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 56)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106544 tablePointerBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 3 (by decide)
    · x86_norm
      exact hP.apart 3 (by decide) 0x654c 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 3 (by decide) 0x6544 57 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6551 (by decide))
  advance_then (mov_m64_r64_effect_step 0x106551 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 72)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106544 tablePointerBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 5 (by decide)
    · x86_norm
      exact hP.apart 5 (by decide) 0x6551 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 5 (by decide) 0x6544 57 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6556 (by decide))
  advance_then (lea_r64_effect_step 0x106556 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 7)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106544 tablePointerBytes 18 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x655b (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x10655b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106544 tablePointerBytes 23 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 4 (by decide)
    · x86_norm
      exact hP.apart 4 (by decide) 0x655b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 4 (by decide) 0x6544 57 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6560 (by decide))
  advance_then (lea_r64_effect_step 0x106560 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106544 tablePointerBytes 28 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6565 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x106565 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106544 tablePointerBytes 33 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.apart 0 (by decide) 0x6565 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0 (by decide) 0x6544 57 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x656a (by decide))
  advance_then (lea_r64_effect_step 0x10656a 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 1896)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106544 tablePointerBytes 38 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6572 (by decide))⟩
  advance_then (lea_r64_effect_step 0x106572 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106544 tablePointerBytes 46 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6577 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x106577 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106544 tablePointerBytes 51 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x657a (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10657a 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106544 tablePointerBytes 54 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x657d (by decide))⟩
  advance_finish [tablePointerEffect, pointerEffect]


end P256.Proofs.Verifying.Combination.Preparation
