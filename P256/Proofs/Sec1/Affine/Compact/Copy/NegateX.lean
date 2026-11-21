import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Copy

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

structure NegateXPre (s : RamState) : Prop where
  rip : s.RIP = 0x110370
  readable : ∀ off ∈ ([280, 288, 296, 304] : List Nat), MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([168, 176, 184, 192] : List Nat), Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([168, 176, 184, 192] : List Nat), ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
      (P256.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 pc) len

def negateXBytes : List UInt8 := [0x48,0x8b,0x84,0x24,0x30,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0xc0,0x0,0x0,0x0,0x48,0x8b,0x84,0x24,0x28,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0xb8,0x0,0x0,0x0,0x48,0x8b,0x84,0x24,0x18,0x1,0x0,0x0,0x48,0x8b,0x8c,0x24,0x20,0x1,0x0,0x0,0x48,0x89,0x8c,0x24,0xb0,0x0,0x0,0x0,0x48,0x89,0x84,0x24,0xa8,0x0,0x0,0x0]

def negateXEffect (s : RamState) : Effect :=
  { rip := 0x1103b0
    writes := [⟨(.mem (stackPtr s + 168) : Operand 64), memLoad s.external (stackPtr s + 280) 64⟩,
      ⟨(.mem (stackPtr s + 176) : Operand 64), memLoad s.external (stackPtr s + 288) 64⟩,
      ⟨(.mem (stackPtr s + 184) : Operand 64), memLoad s.external (stackPtr s + 296) 64⟩,
      ⟨(.mem (stackPtr s + 192) : Operand 64), memLoad s.external (stackPtr s + 304) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 280) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 288) 64⟩] }

set_option maxHeartbeats 800000 in
theorem negateX_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary NegateXPre (codeRange 0x110370 negateXBytes) (Effect.post negateXEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110370 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 304)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 304 (by simp)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10378 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110378 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110370 negateXBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 192 (by simp)
    · x86_norm
      exact hP.codeApart 192 (by simp) 0x10378 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 192 (by simp) 0x10370 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10380 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110380 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 296)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110370 negateXBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 296 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10388 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110388 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110370 negateXBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 184 (by simp)
    · x86_norm
      exact hP.codeApart 184 (by simp) 0x10388 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 184 (by simp) 0x10370 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10390 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110390 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 280)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110370 negateXBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 280 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10398 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110398 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 288)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110370 negateXBytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 288 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x103a0 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1103a0 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110370 negateXBytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 176 (by simp)
    · x86_norm
      exact hP.codeApart 176 (by simp) 0x103a0 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 176 (by simp) 0x10370 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x103a8 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1103a8 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110370 negateXBytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 168 (by simp)
    · x86_norm
      exact hP.codeApart 168 (by simp) 0x103a8 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 168 (by simp) 0x10370 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x103b0 (by decide))
  advance_finish [negateXEffect, stackPtr, Operand.read_reg64, X86.State.regValue,
    gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]

end P256.Proofs.Sec1.Affine.Compact.Copy
