import P256.Proofs.Signing.Core.NextNonce.Memory
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

structure SetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x10c9d1
  writable : ∀ off ∈ ([72,296,280,272,288,80] : List Nat), MemWritable s (stackPtr s + BitVec.ofNat 64 off) 8
  apart : ∀ off ∈ ([72,296,280,272,288,80] : List Nat), ∀ co cl : Nat, co + cl ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) 8 (Extracted.textAddress + BitVec.ofNat 64 co) cl

def setupBytes : List UInt8 :=
  [76, 137, 203, 77, 137, 198, 73, 137, 204, 73, 137, 213, 72, 137, 124, 36, 72, 72, 184, 0, 0, 0, 0, 255, 255, 255, 255, 72, 137, 132, 36, 40, 1, 0, 0, 72, 184, 132, 158, 23, 167, 173, 250, 230, 188, 72, 137, 132, 36, 24, 1, 0, 0, 72, 184, 81, 37, 99, 252, 194, 202, 185, 243, 72, 137, 132, 36, 16, 1, 0, 0, 72, 199, 132, 36, 32, 1, 0, 0, 255, 255, 255, 255, 72, 141, 172, 36, 16, 2, 0, 0, 72, 137, 239, 72, 137, 116, 36, 80]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10ca34
    writes := [⟨(.reg 3 : Operand 64), s.regValue .r9⟩,
      ⟨(.reg 14 : Operand 64), s.regValue .r8⟩,
      ⟨(.reg 12 : Operand 64), s.regValue .rcx⟩,
      ⟨(.reg 13 : Operand 64), s.regValue .rdx⟩,
      ⟨(.mem (stackPtr s+72) : Operand 64), s.regValue .rdi⟩,
      ⟨(.mem (stackPtr s+296) : Operand 64), 0xffffffff00000000⟩,
      ⟨(.mem (stackPtr s+280) : Operand 64), 0xbce6faada7179e84⟩,
      ⟨(.reg 0 : Operand 64), 0xf3b9cac2fc632551⟩,
      ⟨(.mem (stackPtr s+272) : Operand 64), 0xf3b9cac2fc632551⟩,
      ⟨(.mem (stackPtr s+288) : Operand 64), 0xffffffffffffffff⟩,
      ⟨(.reg 5 : Operand 64), stackPtr s+528⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s+528⟩,
      ⟨(.mem (stackPtr s+80) : Operand 64), s.regValue .rsi⟩] }

theorem setup_block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SetupPre (codeRange 0x10c9d1 setupBytes) (Effect.post setupEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10c9d1 0x4c 0xcb (by simp [RexWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0xc9d4 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10c9d4 0x4d 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xc9d7 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10c9d7 0x49 0xcc (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 6 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xc9da (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10c9da 0x49 0xd5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 9 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xc9dd (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x10c9dd 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 12 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 72 (by simp)
    · x86_norm
      exact hP.apart 72 (by simp) 0xc9dd 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 72 (by simp) 0xc9d1 99 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc9e2 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10c9e2 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xffffffff00000000)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 17 10
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xc9ec (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x10c9ec 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 296)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 27 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 296 (by simp)
    · x86_norm
      exact hP.apart 296 (by simp) 0xc9ec 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 296 (by simp) 0xc9d1 99 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc9f4 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10c9f4 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xbce6faada7179e84)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 35 10
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xc9fe (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x10c9fe 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 280)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 45 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 280 (by simp)
    · x86_norm
      exact hP.apart 280 (by simp) 0xc9fe 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 280 (by simp) 0xc9d1 99 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xca06 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10ca06 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xf3b9cac2fc632551)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 53 10
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xca10 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x10ca10 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 272)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 63 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 272 (by simp)
    · x86_norm
      exact hP.apart 272 (by simp) 0xca10 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 272 (by simp) 0xc9d1 99 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xca18 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10ca18 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 288)) (by decide) rfl rfl 0xffffffff)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 71 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 288 (by simp)
    · x86_norm
      exact hP.apart 288 (by simp) 0xca18 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 288 (by simp) 0xc9d1 99 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xca24 (by decide))
  advance_then (lea_r64_effect_step 0x10ca24 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 528)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 83 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xca2c (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10ca2c 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 91 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xca2f (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x10ca2f 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10c9d1 setupBytes 94 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 80 (by simp)
    · x86_norm
      exact hP.apart 80 (by simp) 0xca2f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 80 (by simp) 0xc9d1 99 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xca34 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [setupEffect]
  · x86_norm [setupEffect]
    simp only [Operand.read_reg64, State.regValue, gprNumber, gprIndex,
      rexR, modrmReg, Syntax.Reg.fin]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro flag; cases flag <;> x86_norm [setupEffect]
  · x86_norm [setupEffect, stackPtr, Operand.read_reg64, State.regValue]

end P256.Proofs.Signing.Core.Initialize
