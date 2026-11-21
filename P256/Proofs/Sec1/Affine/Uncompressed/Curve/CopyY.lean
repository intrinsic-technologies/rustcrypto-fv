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

structure CopyYPre (s : RamState) : Prop where
  rip : s.RIP = 0x1109fa
  readable : ∀ off ∈ ([448, 456, 464, 472] : List Nat),
    MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([16, 24, 32, 40] : List Nat),
    Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([16, 24, 32, 40] : List Nat),
    ∀ pc len : Nat, pc + len ≤ 118431 →
      RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
        (P256.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 pc) len

def copyYBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xd8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8b, 0x84, 0x24, 0xd0, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x84, 0x24, 0xc0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0xc8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x10]

def copyYEffect (s : RamState) : Effect :=
  { rip := 0x110a2e
    writes := [⟨(.mem (stackPtr s + 16) : Operand 64), memLoad s.external (stackPtr s + 448) 64⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), memLoad s.external (stackPtr s + 456) 64⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), memLoad s.external (stackPtr s + 464) 64⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), memLoad s.external (stackPtr s + 472) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 448) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 456) 64⟩] }

set_option maxHeartbeats 800000 in
theorem copyY_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyYPre (codeRange 0x1109fa copyYBytes)
      (Effect.post copyYEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1109fa 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 472)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 472 (by simp)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10a02 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110a02 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1109fa copyYBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0x10a02 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0x109fa 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a07 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110a07 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 464)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1109fa copyYBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 464 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a0f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110a0f 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1109fa copyYBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 0x10a0f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0x109fa 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a14 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110a14 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 448)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1109fa copyYBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 448 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a1c (by decide))
  advance_then (mov_r64_m64_effect_step 0x110a1c 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 456)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1109fa copyYBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 456 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a24 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110a24 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1109fa copyYBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x10a24 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x109fa 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a29 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110a29 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1109fa copyYBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x10a29 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x109fa 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a2e (by decide))
  advance_finish [copyYEffect, stackPtr, Operand.read_reg64, X86.State.regValue,
    gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
