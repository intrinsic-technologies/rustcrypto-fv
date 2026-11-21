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

structure ArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x10ca39
  writable : ∀ off ∈ ([88] : List Nat), MemWritable s (stackPtr s + BitVec.ofNat 64 off) 8
  apart : ∀ off ∈ ([88] : List Nat), ∀ co cl : Nat, co + cl ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) 8 (Extracted.textAddress + BitVec.ofNat 64 co) cl

def argumentsBytes : List UInt8 :=
  [72, 141, 132, 36, 16, 1, 0, 0, 72, 141, 188, 36, 112, 8, 0, 0, 65, 191, 32, 0, 0, 0, 186, 32, 0, 0, 0, 72, 137, 238, 76, 137, 108, 36, 88, 76, 137, 233, 77, 137, 224, 77, 137, 241, 73, 137, 254]

def argumentsEffect (s : RamState) : Effect :=
  { rip := 0x10ca68
    writes := [⟨(.reg 0 : Operand 64), stackPtr s+272⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s+2160⟩,
      ⟨(.reg 15 : Operand 64), 32⟩,⟨(.reg 2 : Operand 64), 32⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .rbp⟩,
      ⟨(.mem (stackPtr s+88) : Operand 64), s.regValue .r13⟩,
      ⟨(.reg 1 : Operand 64), s.regValue .r13⟩,
      ⟨(.reg 8 : Operand 64), s.regValue .r12⟩,
      ⟨(.reg 9 : Operand 64), s.regValue .r14⟩,
      ⟨(.reg 14 : Operand 64), stackPtr s+2160⟩] }

theorem arguments_block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ArgumentsPre (codeRange 0x10ca39 argumentsBytes) (Effect.post argumentsEffect) := by
  advance_begin (lea_r64_effect_step 0x10ca39 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 272)) (by decide) rfl rfl)
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0xca41 (by decide))
  advance_then (lea_r64_effect_step 0x10ca41 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 2160)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ca39 argumentsBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xca49 (by decide))⟩
  advance_then (mov_r32_imm32_rex_effect_step 0x10ca49 0x41 0xbf (by simp [RexNoWPrefix]) (by decide) 32)
  case sub => exact codeRange_slice_subset 0x10ca39 argumentsBytes 16 6
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xca4f (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x10ca4f 0xba (by decide) 32)
  case sub => exact codeRange_slice_subset 0x10ca39 argumentsBytes 22 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xca54 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10ca54 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ca39 argumentsBytes 27 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xca57 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x10ca57 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ca39 argumentsBytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 88 (by simp)
    · x86_norm
      exact hP.apart 88 (by simp) 0xca57 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 88 (by simp) 0xca39 47 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xca5c (by decide))
  advance_then (mov_r64_r64_effect_step 0x10ca5c 0x4c 0xe9 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ca39 argumentsBytes 35 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xca5f (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10ca5f 0x4d 0xe0 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ca39 argumentsBytes 38 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xca62 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10ca62 0x4d 0xf1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ca39 argumentsBytes 41 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xca65 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10ca65 0x49 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10ca39 argumentsBytes 44 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xca68 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [argumentsEffect]
  · x86_norm [argumentsEffect]
    simp only [Operand.read_reg64, State.regValue, gprNumber, gprIndex,
      rexR, modrmReg, Syntax.Reg.fin]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro flag; cases flag <;> x86_norm [argumentsEffect]
  · x86_norm [argumentsEffect, stackPtr, Operand.read_reg64, State.regValue]

end P256.Proofs.Signing.Core.Initialize
