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

structure OutputXPre (s : RamState) : Prop where
  rip : s.RIP = 0x110b5a
  readable : ∀ off ∈ ([480, 488, 496, 504] : List Nat),
    MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([512, 520, 528, 536] : List Nat),
    Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([512, 520, 528, 536] : List Nat),
    ∀ pc len : Nat, pc + len ≤ 118431 →
      RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
        (P256.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 pc) len

def outputXBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xe0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0xe8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x0, 0x2, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0x8, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0xf0, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0xf8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x18, 0x2, 0x0, 0x0]

def outputXEffect (s : RamState) : Effect :=
  { rip := 0x110b9a
    writes := [⟨(.mem (stackPtr s + 512) : Operand 64), memLoad s.external (stackPtr s + 480) 64⟩,
      ⟨(.mem (stackPtr s + 520) : Operand 64), memLoad s.external (stackPtr s + 488) 64⟩,
      ⟨(.mem (stackPtr s + 528) : Operand 64), memLoad s.external (stackPtr s + 496) 64⟩,
      ⟨(.mem (stackPtr s + 536) : Operand 64), memLoad s.external (stackPtr s + 504) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 504) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 488) 64⟩] }

set_option maxHeartbeats 800000 in
theorem outputX_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OutputXPre (codeRange 0x110b5a outputXBytes)
      (Effect.post outputXEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110b5a 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 480)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 480 (by simp)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10b62 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110b62 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 488)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b5a outputXBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 488 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10b6a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110b6a 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 512)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b5a outputXBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 512 (by simp)
    · x86_norm
      exact hP.codeApart 512 (by simp) 0x10b6a 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 512 (by simp) 0x10b5a 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10b72 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110b72 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d32 520)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b5a outputXBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 520 (by simp)
    · x86_norm
      exact hP.codeApart 520 (by simp) 0x10b72 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 520 (by simp) 0x10b5a 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10b7a (by decide))
  advance_then (mov_r64_m64_effect_step 0x110b7a 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 496)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b5a outputXBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 496 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10b82 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110b82 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 528)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b5a outputXBytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 528 (by simp)
    · x86_norm
      exact hP.codeApart 528 (by simp) 0x10b82 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 528 (by simp) 0x10b5a 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10b8a (by decide))
  advance_then (mov_r64_m64_effect_step 0x110b8a 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 504)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b5a outputXBytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 504 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10b92 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110b92 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 536)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110b5a outputXBytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 536 (by simp)
    · x86_norm
      exact hP.codeApart 536 (by simp) 0x10b92 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 536 (by simp) 0x10b5a 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10b9a (by decide))
  advance_finish [outputXEffect, stackPtr, Operand.read_reg64, X86.State.regValue,
    gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
