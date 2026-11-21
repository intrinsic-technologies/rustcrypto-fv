import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

structure CopyYPre (s : RamState) : Prop where
  rip : s.RIP = 0x110bfc
  readable : ∀ off ∈ ([544, 552, 560, 568] : List Nat),
    MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([48, 56, 64, 72] : List Nat),
    Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([48, 56, 64, 72] : List Nat),
    ∀ pc len : Nat, pc + len ≤ 118431 →
      RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
        (P256.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 pc) len

def copyYBytes : List UInt8 := [0x48, 0x8b, 0x8c, 0x24, 0x38, 0x2, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x48, 0x48, 0x8b, 0x8c, 0x24, 0x30, 0x2, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x40, 0x48, 0x8b, 0x8c, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x38, 0x48, 0x8b, 0x8c, 0x24, 0x20, 0x2, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x30]

def copyYEffect (s : RamState) : Effect :=
  { rip := 0x110c30
    writes := [⟨(.mem (stackPtr s + 48) : Operand 64), memLoad s.external (stackPtr s + 544) 64⟩,
      ⟨(.mem (stackPtr s + 56) : Operand 64), memLoad s.external (stackPtr s + 552) 64⟩,
      ⟨(.mem (stackPtr s + 64) : Operand 64), memLoad s.external (stackPtr s + 560) 64⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 64), memLoad s.external (stackPtr s + 568) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 544) 64⟩] }

set_option maxHeartbeats 800000 in
theorem copyY_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyYPre (codeRange 0x110bfc copyYBytes)
      (Effect.post copyYEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110bfc 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 568)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 568 (by simp)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10c04 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110c04 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110bfc copyYBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 72 (by simp)
    · x86_norm
      exact hP.codeApart 72 (by simp) 0x10c04 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 72 (by simp) 0x10bfc 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c09 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110c09 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 560)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110bfc copyYBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 560 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c11 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110c11 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110bfc copyYBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 64 (by simp)
    · x86_norm
      exact hP.codeApart 64 (by simp) 0x10c11 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 64 (by simp) 0x10bfc 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c16 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110c16 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 552)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110bfc copyYBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 552 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c1e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110c1e 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110bfc copyYBytes 34 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      exact hP.codeApart 56 (by simp) 0x10c1e 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by simp) 0x10bfc 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c23 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110c23 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 544)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110bfc copyYBytes 39 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 544 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c2b (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110c2b 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110bfc copyYBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.codeApart 48 (by simp) 0x10c2b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp) 0x10bfc 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c30 (by decide))
  advance_finish [copyYEffect, stackPtr, Operand.read_reg64, X86.State.regValue,
    gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]

end P256.Proofs.Sec1.Affine.Uncompressed.Output
