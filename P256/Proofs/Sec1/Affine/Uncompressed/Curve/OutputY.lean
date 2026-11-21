import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

structure OutputYPre (s : RamState) : Prop where
  rip : s.RIP = 0x110b9a
  readable : ∀ off ∈ ([448, 456, 464, 472] : List Nat),
    MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([544, 552, 560, 568] : List Nat),
    Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([544, 552, 560, 568] : List Nat),
    ∀ pc len : Nat, pc + len ≤ 118431 →
      RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
        (P256.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 pc) len

def outputYBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xc0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0xc8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x20, 0x2, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0xd0, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x30, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0xd8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x38, 0x2, 0x0, 0x0]

def outputYEffect (s : RamState) : Effect :=
  { rip := 0x110bda
    writes := [⟨(.mem (stackPtr s + 544) : Operand 64), memLoad s.external (stackPtr s + 448) 64⟩,
      ⟨(.mem (stackPtr s + 552) : Operand 64), memLoad s.external (stackPtr s + 456) 64⟩,
      ⟨(.mem (stackPtr s + 560) : Operand 64), memLoad s.external (stackPtr s + 464) 64⟩,
      ⟨(.mem (stackPtr s + 568) : Operand 64), memLoad s.external (stackPtr s + 472) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 472) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 456) 64⟩] }

set_option maxHeartbeats 800000 in
theorem outputY_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OutputYPre (codeRange 0x110b9a outputYBytes)
      (Effect.post outputYEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110b9a 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 448)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 448 (by simp)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10ba2 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110ba2 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 456)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b9a outputYBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 456 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10baa (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110baa 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 544)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b9a outputYBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 544 (by simp)
    · x86_norm
      exact hP.codeApart 544 (by simp) 0x10baa 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 544 (by simp) 0x10b9a 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10bb2 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110bb2 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 552)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b9a outputYBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 552 (by simp)
    · x86_norm
      exact hP.codeApart 552 (by simp) 0x10bb2 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 552 (by simp) 0x10b9a 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10bba (by decide))
  advance_then (mov_r64_m64_effect_step 0x110bba 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 464)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b9a outputYBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 464 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10bc2 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110bc2 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 560)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b9a outputYBytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 560 (by simp)
    · x86_norm
      exact hP.codeApart 560 (by simp) 0x10bc2 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 560 (by simp) 0x10b9a 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10bca (by decide))
  advance_then (mov_r64_m64_effect_step 0x110bca 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 472)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b9a outputYBytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 472 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10bd2 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110bd2 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 568)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b9a outputYBytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 568 (by simp)
    · x86_norm
      exact hP.codeApart 568 (by simp) 0x10bd2 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 568 (by simp) 0x10b9a 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10bda (by decide))
  advance_finish [outputYEffect, stackPtr, Operand.read_reg64, X86.State.regValue,
    gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
