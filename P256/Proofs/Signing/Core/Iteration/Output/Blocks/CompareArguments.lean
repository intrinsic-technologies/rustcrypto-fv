import P256.Proofs.Signing.Core.Iteration.Stages
import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Common.Field

structure CompareArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x10d428
  readable : ∀ off ∈ ([528, 536, 544, 552] : List Nat), MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([528, 536, 544, 552] : List Nat), MemWritable s (stackPtr s + BitVec.ofNat 64 off) 8
  apart : ∀ off ∈ ([528, 536, 544, 552] : List Nat), ∀ co cl : Nat, co + cl ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) 8 (Extracted.textAddress + BitVec.ofNat 64 co) cl

def CompareArgumentsBytes : List UInt8 :=
  [72, 139, 132, 36, 40, 2, 0, 0, 72, 15, 200, 72, 139, 140, 36, 32, 2, 0, 0, 72, 15, 201, 72, 139, 148, 36, 16, 2, 0, 0, 72, 139, 180, 36, 24, 2, 0, 0, 72, 15, 206, 72, 15, 202, 72, 137, 132, 36, 16, 2, 0, 0, 72, 137, 140, 36, 24, 2, 0, 0, 72, 137, 180, 36, 32, 2, 0, 0, 72, 137, 148, 36, 40, 2, 0, 0, 72, 141, 180, 36, 16, 2, 0, 0, 186, 32, 0, 0, 0, 76, 137, 247]

def CompareArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x10d484
    writes := [⟨(.reg 0 : Operand 64), Common.Instructions.bswap64 ((Operand.mem (stackPtr s + 552) : Operand 64).read s)⟩,
      ⟨(.reg 1 : Operand 64), Common.Instructions.bswap64 ((Operand.mem (stackPtr s + 544) : Operand 64).read s)⟩,
      ⟨(.reg 2 : Operand 64), 32⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 528⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 528) : Operand 64), Common.Instructions.bswap64 ((Operand.mem (stackPtr s + 552) : Operand 64).read s)⟩,
      ⟨(.mem (stackPtr s + 536) : Operand 64), Common.Instructions.bswap64 ((Operand.mem (stackPtr s + 544) : Operand 64).read s)⟩,
      ⟨(.mem (stackPtr s + 544) : Operand 64), Common.Instructions.bswap64 ((Operand.mem (stackPtr s + 536) : Operand 64).read s)⟩,
      ⟨(.mem (stackPtr s + 552) : Operand 64), Common.Instructions.bswap64 ((Operand.mem (stackPtr s + 528) : Operand 64).read s)⟩] }

set_option maxHeartbeats 1000000 in
theorem CompareArguments_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CompareArgumentsPre (codeRange 0x10d428 CompareArgumentsBytes) (Effect.post CompareArgumentsEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10d428 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 552)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 552 (by simp)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd430 (by decide))
  advance_then (P256.Proofs.Common.Instructions.bswap_r64_effect_step 0x10d430 0)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), (Effect.Avoids.of_noMem (by simp [Common.Instructions.bswapR64Effect,Effect.components,Component.Covers]) _), ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd433 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d433 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 544)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 11 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 544 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd43b (by decide))
  advance_then (P256.Proofs.Common.Instructions.bswap_r64_effect_step 0x10d43b 1)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), (Effect.Avoids.of_noMem (by simp [Common.Instructions.bswapR64Effect,Effect.components,Component.Covers]) _), ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd43e (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d43e 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 528)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 22 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 528 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd446 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d446 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 536)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 30 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 536 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd44e (by decide))
  advance_then (P256.Proofs.Common.Instructions.bswap_r64_effect_step 0x10d44e 6)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 38 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), (Effect.Avoids.of_noMem (by simp [Common.Instructions.bswapR64Effect,Effect.components,Component.Covers]) _), ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd451 (by decide))
  advance_then (P256.Proofs.Common.Instructions.bswap_r64_effect_step 0x10d451 2)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 41 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), (Effect.Avoids.of_noMem (by simp [Common.Instructions.bswapR64Effect,Effect.components,Component.Covers]) _), ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd454 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d454 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 528)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 44 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 528 (by simp)
    · x86_norm
      exact hP.apart 528 (by simp) 0xd454 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 528 (by simp) 0xd428 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd45c (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d45c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 536)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 52 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 536 (by simp)
    · x86_norm
      exact hP.apart 536 (by simp) 0xd45c 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 536 (by simp) 0xd428 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd464 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d464 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 544)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 60 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 544 (by simp)
    · x86_norm
      exact hP.apart 544 (by simp) 0xd464 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 544 (by simp) 0xd428 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd46c (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d46c 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 552)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 68 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 552 (by simp)
    · x86_norm
      exact hP.apart 552 (by simp) 0xd46c 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 552 (by simp) 0xd428 92 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd474 (by decide))
  advance_then (lea_r64_effect_step 0x10d474 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 528)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 76 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), (Effect.Avoids.of_noMem (by simp [Component.Covers]) _), ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd47c (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10d47c 0xba (by decide) 32)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 84 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), (Effect.Avoids.of_noMem (by simp [Component.Covers]) _), ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd481 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10d481 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d428 CompareArgumentsBytes 89 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), (Effect.Avoids.of_noMem (by simp [Component.Covers]) _), ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd484 (by decide))
  advance_finish [CompareArgumentsEffect, stackPtr, Operand.read_reg64, State.regValue, gprNumber]

end P256.Proofs.Signing.Core.Iteration.Output.Blocks
