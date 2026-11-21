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

structure NegateYPre (s : RamState) : Prop where
  rip : s.RIP = 0x110318
  readable : ∀ off ∈ ([312, 320, 328, 336] : List Nat), MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([344, 352, 360, 368] : List Nat), Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([344, 352, 360, 368] : List Nat), ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
      (P256.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 pc) len

def negateYBytes : List UInt8 := [0x48,0x8b,0x84,0x24,0x50,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x70,0x1,0x0,0x0,0x48,0x8b,0x84,0x24,0x48,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x68,0x1,0x0,0x0,0x48,0x8b,0x84,0x24,0x38,0x1,0x0,0x0,0x48,0x8b,0x8c,0x24,0x40,0x1,0x0,0x0,0x48,0x89,0x8c,0x24,0x60,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x58,0x1,0x0,0x0]

def negateYEffect (s : RamState) : Effect :=
  { rip := 0x110358
    writes := [⟨(.mem (stackPtr s + 344) : Operand 64), memLoad s.external (stackPtr s + 312) 64⟩,
      ⟨(.mem (stackPtr s + 352) : Operand 64), memLoad s.external (stackPtr s + 320) 64⟩,
      ⟨(.mem (stackPtr s + 360) : Operand 64), memLoad s.external (stackPtr s + 328) 64⟩,
      ⟨(.mem (stackPtr s + 368) : Operand 64), memLoad s.external (stackPtr s + 336) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 312) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 320) 64⟩] }

set_option maxHeartbeats 800000 in
theorem negateY_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary NegateYPre (codeRange 0x110318 negateYBytes) (Effect.post negateYEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110318 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 336)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 336 (by simp)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10320 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110320 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 368)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110318 negateYBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 368 (by simp)
    · x86_norm
      exact hP.codeApart 368 (by simp) 0x10320 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 368 (by simp) 0x10318 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10328 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110328 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 328)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110318 negateYBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 328 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10330 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110330 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 360)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110318 negateYBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 360 (by simp)
    · x86_norm
      exact hP.codeApart 360 (by simp) 0x10330 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 360 (by simp) 0x10318 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10338 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110338 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 312)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110318 negateYBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 312 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10340 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110340 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 320)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110318 negateYBytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 320 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10348 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110348 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 352)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110318 negateYBytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 352 (by simp)
    · x86_norm
      exact hP.codeApart 352 (by simp) 0x10348 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 352 (by simp) 0x10318 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10350 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110350 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 344)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110318 negateYBytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 344 (by simp)
    · x86_norm
      exact hP.codeApart 344 (by simp) 0x10350 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 344 (by simp) 0x10318 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10358 (by decide))
  advance_finish [negateYEffect, stackPtr, Operand.read_reg64, X86.State.regValue,
    gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]

end P256.Proofs.Sec1.Affine.Compact.Copy
