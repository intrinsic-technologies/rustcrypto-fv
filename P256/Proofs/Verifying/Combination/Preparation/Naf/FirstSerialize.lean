import P256.Proofs.Verifying.Combination.Entry
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf.FirstSerialize

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10664e
  writable : ∀ k < 4, MemWritable s ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 (24+8*k)) 8
  apart : ∀ k < 4, ∀ offset len : Nat, offset+len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 (24+8*k)) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48, 0x8d, 0x84, 0x24, 0x38, 0x1, 0x0, 0x0, 0x48, 0x89, 0x5c, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x8d, 0x44, 0x24, 0x7, 0x48, 0x89, 0x44, 0x24, 0x28, 0x4c, 0x89, 0x7c, 0x24, 0x18, 0x48, 0x8d, 0x9c, 0x24, 0x38, 0x1, 0x0, 0x0, 0x48, 0x8d, 0x6c, 0x24, 0x18, 0x48, 0x89, 0xdf, 0x48, 0x89, 0xee]

def effect (s : RamState) : Effect :=
  { rip := 0x106682
    writes := [⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 48) : Operand 64), (Operand.reg 4 : Operand 64).read s + 312⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 40) : Operand 64), (Operand.reg 4 : Operand 64).read s + 7⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(Operand.reg 0 : Operand 64), (Operand.reg 4 : Operand 64).read s + 7⟩,
      ⟨(Operand.reg 3 : Operand 64), (Operand.reg 4 : Operand 64).read s + 312⟩,
      ⟨(Operand.reg 5 : Operand 64), (Operand.reg 4 : Operand 64).read s + 24⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 312⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 24⟩] }

set_option maxHeartbeats 800000 in
theorem run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10664e bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10664e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x6656 (by decide))
  advance_then (mov_m64_r64_effect_step 0x106656 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 32)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10664e bytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1 (by decide)
    · x86_norm
      exact hP.apart 1 (by decide) 0x6656 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1 (by decide) 0x664e 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x665b (by decide))
  advance_then (mov_m64_r64_effect_step 0x10665b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 48)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10664e bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 3 (by decide)
    · x86_norm
      exact hP.apart 3 (by decide) 0x665b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 3 (by decide) 0x664e 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6660 (by decide))
  advance_then (lea_r64_effect_step 0x106660 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 7)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10664e bytes 18 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6665 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x106665 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10664e bytes 23 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 2 (by decide)
    · x86_norm
      exact hP.apart 2 (by decide) 0x6665 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 2 (by decide) 0x664e 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x666a (by decide))
  advance_then (mov_m64_r64_effect_step 0x10666a 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 24)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10664e bytes 28 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.apart 0 (by decide) 0x666a 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0 (by decide) 0x664e 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x666f (by decide))
  advance_then (lea_r64_effect_step 0x10666f 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10664e bytes 33 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6677 (by decide))⟩
  advance_then (lea_r64_effect_step 0x106677 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10664e bytes 41 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x667c (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10667c 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10664e bytes 46 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x667f (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10667f 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10664e bytes 49 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6682 (by decide))⟩
  advance_finish [effect]

end P256.Proofs.Verifying.Combination.Preparation.Naf.FirstSerialize
