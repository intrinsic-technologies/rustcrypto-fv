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

structure XZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x11090a
  byteWritable : MemWritable s (stackPtr s + 48) 1
  writable : ∀ off n, (off,n) ∈ ([(400, 8), (392, 8), (384, 8), (376, 8)] : List (Nat × Nat)) →
    Writable s (stackPtr s + BitVec.ofNat 64 off) n
  codeApart : ∀ off n, (off,n) ∈ ([(48,1), (376,8), (384,8), (392,8), (400,8)] : List (Nat × Nat)) →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) n 0x11090a 52

def xZeroBytes : List UInt8 :=
  [0x88, 0x44, 0x24, 0x30, 0x48, 0xc7, 0x84, 0x24, 0x90, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x88, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x80, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x78, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

def xZeroEffect (s : RamState) : Effect :=
  { rip := 0x11093e
    writes := [⟨(.mem (stackPtr s + 48) : Operand 8), (Operand.reg 0 : Operand 8).read s⟩,
      ⟨(.mem (stackPtr s + 376) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 384) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 392) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 400) : Operand 64), 0⟩] }

set_option maxHeartbeats 800000 in
theorem x_zero_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary XZeroPre (codeRange 0x11090a xZeroBytes)
      xZeroEffect := by
  advance_begin (mov_m8_r8_legacy_effect_step 0x11090a 0 (by decide) (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.byteWritable, (h.codeApart 48 1 (by simp)).sub 0 4 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 48 1 (by simp)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x1090e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x11090e 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 400)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x11090a xZeroBytes 4 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 400 8 (by simp)
    · x86_norm
      exact (hP.codeApart 400 8 (by simp)).sub 4 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 400 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1091a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x11091a 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 392)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x11090a xZeroBytes 16 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 392 8 (by simp)
    · x86_norm
      exact (hP.codeApart 392 8 (by simp)).sub 16 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 392 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10926 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x110926 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 384)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x11090a xZeroBytes 28 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 384 8 (by simp)
    · x86_norm
      exact (hP.codeApart 384 8 (by simp)).sub 28 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 384 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10932 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x110932 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 376)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x11090a xZeroBytes 40 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 376 8 (by simp)
    · x86_norm
      exact (hP.codeApart 376 8 (by simp)).sub 40 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 376 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1093e (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [xZeroEffect, stackPtr, Operand.read_reg64,
      gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
      Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]
    all_goals repeat first | constructor | rfl
  · x86_norm [xZeroEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl
  · intro f; cases f <;> x86_norm [xZeroEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl
  · x86_norm [xZeroEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks
