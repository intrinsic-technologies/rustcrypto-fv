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

structure YPre (s : RamState) : Prop where
  rip : s.RIP = 0x110294
  readable : ∀ off ∈ ([312, 320, 328, 336] : List Nat), MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([128, 136, 144, 152] : List Nat), Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([128, 136, 144, 152] : List Nat), ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
      (P256.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 pc) len

def yBytes : List UInt8 := [0x48,0x8b,0x84,0x24,0x50,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x98,0x0,0x0,0x0,0x48,0x8b,0x84,0x24,0x48,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x90,0x0,0x0,0x0,0x48,0x8b,0x84,0x24,0x40,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x88,0x0,0x0,0x0,0x48,0x8b,0x84,0x24,0x38,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x80,0x0,0x0,0x0]

def yEffect (s : RamState) : Effect :=
  { rip := 0x1102d4
    writes := [⟨(.mem (stackPtr s + 128) : Operand 64), memLoad s.external (stackPtr s + 312) 64⟩,
      ⟨(.mem (stackPtr s + 136) : Operand 64), memLoad s.external (stackPtr s + 320) 64⟩,
      ⟨(.mem (stackPtr s + 144) : Operand 64), memLoad s.external (stackPtr s + 328) 64⟩,
      ⟨(.mem (stackPtr s + 152) : Operand 64), memLoad s.external (stackPtr s + 336) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 312) 64⟩] }

set_option maxHeartbeats 800000 in
theorem y_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary YPre (codeRange 0x110294 yBytes) (Effect.post yEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110294 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 336)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 336 (by simp)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1029c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11029c 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110294 yBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 152 (by simp)
    · x86_norm
      exact hP.codeApart 152 (by simp) 0x1029c 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 152 (by simp) 0x10294 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x102a4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1102a4 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 328)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110294 yBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 328 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x102ac (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1102ac 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110294 yBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 144 (by simp)
    · x86_norm
      exact hP.codeApart 144 (by simp) 0x102ac 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 144 (by simp) 0x10294 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x102b4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1102b4 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 320)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110294 yBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 320 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x102bc (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1102bc 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110294 yBytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by simp)
    · x86_norm
      exact hP.codeApart 136 (by simp) 0x102bc 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 136 (by simp) 0x10294 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x102c4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1102c4 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 312)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110294 yBytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 312 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x102cc (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1102cc 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110294 yBytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 128 (by simp)
    · x86_norm
      exact hP.codeApart 128 (by simp) 0x102cc 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 128 (by simp) 0x10294 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x102d4 (by decide))
  advance_finish [yEffect, stackPtr, Operand.read_reg64, X86.State.regValue,
    gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
    Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]

end P256.Proofs.Sec1.Affine.Compact.Copy
