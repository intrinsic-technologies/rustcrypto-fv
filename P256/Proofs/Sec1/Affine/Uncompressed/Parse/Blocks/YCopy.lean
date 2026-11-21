import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step mov_m8_r8_effect_step)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

structure YCopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x110790
  readable : ∀ off ∈ ([168, 176, 184, 192] : List Nat),
    MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off n, (off,n) ∈ ([(120, 8), (112, 8), (104, 8), (96, 8)] : List (Nat × Nat)) →
    Writable s (stackPtr s + BitVec.ofNat 64 off) n
  codeApart : ∀ off n, (off,n) ∈ ([(96,8), (104,8), (112,8), (120,8)] : List (Nat × Nat)) →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) n 0x110790 52

def yCopyBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xc0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8b, 0x84, 0x24, 0xb8, 0x0, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x8b, 0x84, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x60]

def yCopyEffect (s : RamState) : Effect :=
  { rip := 0x1107c4
    writes := [⟨(.mem (stackPtr s + 96) : Operand 64), memLoad s.external (stackPtr s + 168) 64⟩,
      ⟨(.mem (stackPtr s + 104) : Operand 64), memLoad s.external (stackPtr s + 176) 64⟩,
      ⟨(.mem (stackPtr s + 112) : Operand 64), memLoad s.external (stackPtr s + 184) 64⟩,
      ⟨(.mem (stackPtr s + 120) : Operand 64), memLoad s.external (stackPtr s + 192) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 168) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 176) 64⟩] }

set_option maxHeartbeats 800000 in
theorem y_copy_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary YCopyPre (codeRange 0x110790 yCopyBytes)
      yCopyEffect := by
  advance_begin (mov_r64_m64_effect_step 0x110790 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 192 (by simp)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10798 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110798 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110790 yCopyBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 120 8 (by simp)
    · x86_norm
      exact (hP.codeApart 120 8 (by simp)).sub 8 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 120 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1079d (by decide))
  advance_then (mov_r64_m64_effect_step 0x11079d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110790 yCopyBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 184 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x107a5 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1107a5 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110790 yCopyBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 112 8 (by simp)
    · x86_norm
      exact (hP.codeApart 112 8 (by simp)).sub 21 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 112 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x107aa (by decide))
  advance_then (mov_r64_m64_effect_step 0x1107aa 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110790 yCopyBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 168 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x107b2 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1107b2 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110790 yCopyBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 176 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x107ba (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1107ba 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110790 yCopyBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 104 8 (by simp)
    · x86_norm
      exact (hP.codeApart 104 8 (by simp)).sub 42 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 104 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x107bf (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1107bf 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110790 yCopyBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 96 8 (by simp)
    · x86_norm
      exact (hP.codeApart 96 8 (by simp)).sub 47 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 96 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x107c4 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [yCopyEffect, stackPtr, Operand.read_reg64,
      gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
      Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]
    all_goals repeat first | constructor | rfl
  · x86_norm [yCopyEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl
  · intro f; cases f <;> x86_norm [yCopyEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl
  · x86_norm [yCopyEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks
