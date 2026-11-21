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

structure XArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x10d3dc
  readable : ∀ off ∈ ([104, 112, 120, 128] : List Nat), MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([1328, 1336, 1344, 1352] : List Nat), MemWritable s (stackPtr s + BitVec.ofNat 64 off) 8
  apart : ∀ off ∈ ([1328, 1336, 1344, 1352] : List Nat), ∀ co cl : Nat, co + cl ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) 8 (Extracted.textAddress + BitVec.ofNat 64 co) cl

def XArgumentsBytes : List UInt8 :=
  [72, 139, 132, 36, 128, 0, 0, 0, 72, 137, 132, 36, 72, 5, 0, 0, 72, 139, 68, 36, 120, 72, 137, 132, 36, 64, 5, 0, 0, 72, 139, 68, 36, 104, 72, 139, 76, 36, 112, 72, 137, 140, 36, 56, 5, 0, 0, 72, 137, 132, 36, 48, 5, 0, 0, 72, 141, 188, 36, 16, 2, 0, 0, 72, 141, 180, 36, 48, 5, 0, 0]

def XArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x10d423
    writes := [⟨(.reg 0 : Operand 64), (Operand.mem (stackPtr s + 104) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (Operand.mem (stackPtr s + 112) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 528⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 1328⟩,
      ⟨(.mem (stackPtr s + 1352) : Operand 64), (Operand.mem (stackPtr s + 128) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 1344) : Operand 64), (Operand.mem (stackPtr s + 120) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 1336) : Operand 64), (Operand.mem (stackPtr s + 112) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 1328) : Operand 64), (Operand.mem (stackPtr s + 104) : Operand 64).read s⟩] }

set_option maxHeartbeats 1000000 in
theorem XArguments_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary XArgumentsPre (codeRange 0x10d3dc XArgumentsBytes) (Effect.post XArgumentsEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10d3dc 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 128 (by simp)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd3e4 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d3e4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1352)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d3dc XArgumentsBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1352 (by simp)
    · x86_norm
      exact hP.apart 1352 (by simp) 0xd3e4 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1352 (by simp) 0xd3dc 71 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd3ec (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d3ec 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d3dc XArgumentsBytes 16 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 120 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd3f1 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d3f1 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1344)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d3dc XArgumentsBytes 21 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1344 (by simp)
    · x86_norm
      exact hP.apart 1344 (by simp) 0xd3f1 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1344 (by simp) 0xd3dc 71 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd3f9 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d3f9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d3dc XArgumentsBytes 29 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 104 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd3fe (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d3fe 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d3dc XArgumentsBytes 34 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 112 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd403 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d403 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 1336)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d3dc XArgumentsBytes 39 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1336 (by simp)
    · x86_norm
      exact hP.apart 1336 (by simp) 0xd403 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1336 (by simp) 0xd3dc 71 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd40b (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d40b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1328)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d3dc XArgumentsBytes 47 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1328 (by simp)
    · x86_norm
      exact hP.apart 1328 (by simp) 0xd40b 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1328 (by simp) 0xd3dc 71 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd413 (by decide))
  advance_then (lea_r64_effect_step 0x10d413 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 528)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d3dc XArgumentsBytes 55 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd41b (by decide))
  advance_then (lea_r64_effect_step 0x10d41b 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 1328)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d3dc XArgumentsBytes 63 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd423 (by decide))
  advance_finish [XArgumentsEffect, stackPtr, Operand.read_reg64, State.regValue, gprNumber]

end P256.Proofs.Signing.Core.Iteration.Output.Blocks
