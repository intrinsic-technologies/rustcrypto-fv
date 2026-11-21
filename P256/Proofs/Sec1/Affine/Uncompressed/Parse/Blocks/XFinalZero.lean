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

structure XFinalZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x11099f
  byteWritable : MemWritable s (stackPtr s + 200) 1
  writable : ∀ off n, (off,n) ∈ ([(272, 8), (264, 8), (256, 8), (248, 8)] : List (Nat × Nat)) →
    Writable s (stackPtr s + BitVec.ofNat 64 off) n
  codeApart : ∀ off n, (off,n) ∈ ([(200,1), (248,8), (256,8), (264,8), (272,8)] : List (Nat × Nat)) →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) n 0x11099f 56

def xFinalZeroBytes : List UInt8 :=
  [0x44, 0x88, 0xbc, 0x24, 0xc8, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x10, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x8, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xf8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

def xFinalZeroEffect (s : RamState) : Effect :=
  { rip := 0x1109d7
    writes := [⟨(.mem (stackPtr s + 200) : Operand 8), (Operand.reg 15 : Operand 8).read s⟩,
      ⟨(.mem (stackPtr s + 248) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 256) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 264) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 272) : Operand 64), 0⟩] }

set_option maxHeartbeats 800000 in
theorem x_final_zero_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary XFinalZeroPre (codeRange 0x11099f xFinalZeroBytes)
      xFinalZeroEffect := by
  advance_begin (mov_m8_r8_effect_step 0x11099f 0x44 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.byteWritable, (h.codeApart 200 1 (by simp)).sub 0 8 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 200 1 (by simp)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x109a7 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1109a7 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 272)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x11099f xFinalZeroBytes 8 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 272 8 (by simp)
    · x86_norm
      exact (hP.codeApart 272 8 (by simp)).sub 8 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 272 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x109b3 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1109b3 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 264)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x11099f xFinalZeroBytes 20 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 264 8 (by simp)
    · x86_norm
      exact (hP.codeApart 264 8 (by simp)).sub 20 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 264 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x109bf (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1109bf 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 256)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x11099f xFinalZeroBytes 32 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 256 8 (by simp)
    · x86_norm
      exact (hP.codeApart 256 8 (by simp)).sub 32 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 256 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x109cb (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1109cb 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 248)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x11099f xFinalZeroBytes 44 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 248 8 (by simp)
    · x86_norm
      exact (hP.codeApart 248 8 (by simp)).sub 44 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 248 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x109d7 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [xFinalZeroEffect, stackPtr, Operand.read_reg64,
      gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
      Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]
    all_goals repeat first | constructor | rfl
  · x86_norm [xFinalZeroEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl
  · intro f; cases f <;> x86_norm [xFinalZeroEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl
  · x86_norm [xFinalZeroEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks
