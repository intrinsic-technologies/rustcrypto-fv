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

structure CopyXPre (s : RamState) : Prop where
  rip : s.RIP = 0x110a46
  readable : ∀ off ∈ ([480, 488, 496, 504] : List Nat),
    MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([16, 24, 32, 40] : List Nat),
    Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([16, 24, 32, 40] : List Nat),
    ∀ pc len : Nat, pc + len ≤ 118431 →
      RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
        (P256.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 pc) len

def copyXBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xf8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8b, 0x84, 0x24, 0xf0, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x84, 0x24, 0xe0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0xe8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x10]

def copyXEffect (s : RamState) : Effect :=
  { rip := 0x110a7a
    writes := [⟨(.mem (stackPtr s + 16) : Operand 64), memLoad s.external (stackPtr s + 480) 64⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), memLoad s.external (stackPtr s + 488) 64⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), memLoad s.external (stackPtr s + 496) 64⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), memLoad s.external (stackPtr s + 504) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 480) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 488) 64⟩] }

set_option maxHeartbeats 800000 in
theorem copyX_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyXPre (codeRange 0x110a46 copyXBytes)
      (Effect.post copyXEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110a46 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 504)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 504 (by simp)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10a4e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110a4e 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110a46 copyXBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0x10a4e 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0x10a46 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a53 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110a53 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 496)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110a46 copyXBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 496 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a5b (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110a5b 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110a46 copyXBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 0x10a5b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0x10a46 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a60 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110a60 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 480)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110a46 copyXBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 480 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a68 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110a68 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 488)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110a46 copyXBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 488 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a70 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110a70 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110a46 copyXBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x10a70 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x10a46 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a75 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110a75 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110a46 copyXBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x10a75 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x10a46 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a7a (by decide))
  advance_finish [copyXEffect, stackPtr, Operand.read_reg64, X86.State.regValue,
    gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
