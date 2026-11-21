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

structure CopyXPre (s : RamState) : Prop where
  rip : s.RIP = 0x110c30
  readable : ∀ off ∈ ([512, 520, 528, 536] : List Nat),
    MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([16, 24, 32, 40] : List Nat),
    Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([16, 24, 32, 40] : List Nat),
    ∀ pc len : Nat, pc + len ≤ 118431 →
      RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
        (P256.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 pc) len

def copyXBytes : List UInt8 :=
  [0x48, 0x8b, 0x8c, 0x24, 0x18, 0x2, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x28, 0x48, 0x8b, 0x8c, 0x24, 0x10, 0x2, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x20, 0x48, 0x8b, 0x8c, 0x24, 0x0, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x94, 0x24, 0x8, 0x2, 0x0, 0x0, 0x48, 0x89, 0x54, 0x24, 0x18, 0x48, 0x89, 0x4c, 0x24, 0x10]

def copyXEffect (s : RamState) : Effect :=
  { rip := 0x110c64
    writes := [⟨(.mem (stackPtr s + 16) : Operand 64), memLoad s.external (stackPtr s + 512) 64⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), memLoad s.external (stackPtr s + 520) 64⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), memLoad s.external (stackPtr s + 528) 64⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), memLoad s.external (stackPtr s + 536) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 512) 64⟩,
      ⟨(.reg 2 : Operand 64), memLoad s.external (stackPtr s + 520) 64⟩] }

set_option maxHeartbeats 800000 in
theorem copyX_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyXPre (codeRange 0x110c30 copyXBytes)
      (Effect.post copyXEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110c30 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 536)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 536 (by simp)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10c38 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110c38 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110c30 copyXBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0x10c38 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0x10c30 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c3d (by decide))
  advance_then (mov_r64_m64_effect_step 0x110c3d 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 528)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110c30 copyXBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 528 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c45 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110c45 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110c30 copyXBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 0x10c45 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0x10c30 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c4a (by decide))
  advance_then (mov_r64_m64_effect_step 0x110c4a 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 512)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110c30 copyXBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 512 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c52 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110c52 0x48 (by simp [RexWPrefix])
    2 (.sib 4 none 0 (.d32 520)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110c30 copyXBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 520 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c5a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110c5a 0x48 (by simp [RexWPrefix])
    2 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110c30 copyXBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x10c5a 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x10c30 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c5f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110c5f 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110c30 copyXBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x10c5f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x10c30 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10c64 (by decide))
  advance_finish [copyXEffect, stackPtr, Operand.read_reg64, X86.State.regValue,
    gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]

end P256.Proofs.Sec1.Affine.Uncompressed.Output
