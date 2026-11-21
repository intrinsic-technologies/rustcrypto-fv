import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

structure XPre (s : RamState) : Prop where
  rip : s.RIP = 0x110500
  readable : ∀ off ∈ ([280, 288, 296, 304] : List Nat), MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([640, 648, 656, 664] : List Nat), Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([640, 648, 656, 664] : List Nat), ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
      (P256.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 pc) len

def xBytes : List UInt8 := [0x48,0x8b,0x84,0x24,0x30,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x98,0x2,0x0,0x0,0x48,0x8b,0x84,0x24,0x28,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x90,0x2,0x0,0x0,0x48,0x8b,0x84,0x24,0x18,0x1,0x0,0x0,0x48,0x8b,0x8c,0x24,0x20,0x1,0x0,0x0,0x48,0x89,0x8c,0x24,0x88,0x2,0x0,0x0,0x48,0x89,0x84,0x24,0x80,0x2,0x0,0x0]

def xEffect (s : RamState) : Effect :=
  { rip := 0x110540
    writes := [⟨(.mem (stackPtr s + 640) : Operand 64), memLoad s.external (stackPtr s + 280) 64⟩,
      ⟨(.mem (stackPtr s + 648) : Operand 64), memLoad s.external (stackPtr s + 288) 64⟩,
      ⟨(.mem (stackPtr s + 656) : Operand 64), memLoad s.external (stackPtr s + 296) 64⟩,
      ⟨(.mem (stackPtr s + 664) : Operand 64), memLoad s.external (stackPtr s + 304) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 280) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 288) 64⟩] }

set_option maxHeartbeats 800000 in
theorem x_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary XPre (codeRange 0x110500 xBytes) (Effect.post xEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110500 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 304)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 304 (by simp)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10508 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110508 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 664)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110500 xBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 664 (by simp)
    · x86_norm
      exact hP.codeApart 664 (by simp) 0x10508 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 664 (by simp) 0x10500 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10510 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110510 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 296)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110500 xBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 296 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10518 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110518 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 656)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110500 xBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 656 (by simp)
    · x86_norm
      exact hP.codeApart 656 (by simp) 0x10518 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 656 (by simp) 0x10500 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10520 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110520 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 280)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110500 xBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 280 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10528 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110528 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 288)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110500 xBytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 288 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10530 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110530 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 648)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110500 xBytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 648 (by simp)
    · x86_norm
      exact hP.codeApart 648 (by simp) 0x10530 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 648 (by simp) 0x10500 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10538 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110538 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 640)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110500 xBytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 640 (by simp)
    · x86_norm
      exact hP.codeApart 640 (by simp) 0x10538 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 640 (by simp) 0x10500 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10540 (by decide))
  advance_finish [xEffect, stackPtr, Operand.read_reg64, X86.State.regValue,
    gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]

end P256.Proofs.Sec1.Affine.Compact.Finish
