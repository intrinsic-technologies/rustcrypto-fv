import P256.Proofs.Verifying.Combination.Entry
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf.Store

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10673e
  writable : ∀ k < 6, MemWritable s ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 (312+8*k)) 8
  apart : ∀ k < 6, ∀ offset len : Nat, offset+len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 (312+8*k)) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48, 0x8d, 0x84, 0x24, 0x68, 0x13, 0x0, 0x0, 0x48, 0x8d, 0x8c, 0x24, 0x88, 0x9, 0x0, 0x0, 0x48, 0x8d, 0x94, 0x24, 0x68, 0xd, 0x0, 0x0, 0x48, 0x89, 0x94, 0x24, 0x38, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x40, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xbc, 0x24, 0x48, 0x1, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0x50, 0x1, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x58, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x60, 0x1, 0x0, 0x0, 0x2, 0x0, 0x0, 0x0, 0x48, 0x8d, 0xb4, 0x24, 0x38, 0x1, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x106796
    writes := [⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 312) : Operand 64), (Operand.reg 4 : Operand 64).read s + 3432⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 320) : Operand 64), (Operand.reg 4 : Operand 64).read s + 4968⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 328) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 336) : Operand 64), (Operand.reg 4 : Operand 64).read s + 2440⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 344) : Operand 64), 0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 352) : Operand 64), 2⟩,
      ⟨(Operand.reg 0 : Operand 64), (Operand.reg 4 : Operand 64).read s + 4968⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.reg 4 : Operand 64).read s + 2440⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 3432⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 312⟩] }

set_option maxHeartbeats 800000 in
theorem run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10673e bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10673e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 4968)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x6746 (by decide))
  advance_then (lea_r64_effect_step 0x106746 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 2440)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10673e bytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x674e (by decide))⟩
  advance_then (lea_r64_effect_step 0x10674e 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 3432)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10673e bytes 16 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6756 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x106756 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 312)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10673e bytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.apart 0 (by decide) 0x6756 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0 (by decide) 0x673e 88 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x675e (by decide))
  advance_then (mov_m64_r64_effect_step 0x10675e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 320)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10673e bytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1 (by decide)
    · x86_norm
      exact hP.apart 1 (by decide) 0x675e 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1 (by decide) 0x673e 88 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6766 (by decide))
  advance_then (mov_m64_r64_effect_step 0x106766 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 328)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10673e bytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 2 (by decide)
    · x86_norm
      exact hP.apart 2 (by decide) 0x6766 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 2 (by decide) 0x673e 88 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x676e (by decide))
  advance_then (mov_m64_r64_effect_step 0x10676e 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 336)) (by constructor <;> decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10673e bytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 3 (by decide)
    · x86_norm
      exact hP.apart 3 (by decide) 0x676e 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 3 (by decide) 0x673e 88 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6776 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x106776 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 344)) (by constructor <;> decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10673e bytes 56 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 4 (by decide)
    · x86_norm
      exact hP.apart 4 (by decide) 0x6776 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 4 (by decide) 0x673e 88 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6782 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x106782 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 352)) (by constructor <;> decide +kernel) rfl rfl 2)
  case sub => exact codeRange_slice_subset 0x10673e bytes 68 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 5 (by decide)
    · x86_norm
      exact hP.apart 5 (by decide) 0x6782 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 5 (by decide) 0x673e 88 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x678e (by decide))
  advance_then (lea_r64_effect_step 0x10678e 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10673e bytes 80 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6796 (by decide))⟩
  advance_finish [effect]

end P256.Proofs.Verifying.Combination.Preparation.Naf.Store
