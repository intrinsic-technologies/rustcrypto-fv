import P256.Proofs.Projective.Multiply.Machine.Radix.Store
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

structure YFinalZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x1107c4
  byteWritable : MemWritable s (stackPtr s + 128) 1
  writable : ∀ off n, (off,n) ∈ ([(12, 4), (632, 8), (624, 8), (616, 8), (608, 8)] : List (Nat × Nat)) →
    Writable s (stackPtr s + BitVec.ofNat 64 off) n
  codeApart : ∀ off n, (off,n) ∈ ([(12,4), (128,1), (608,8), (616,8), (624,8), (632,8)] : List (Nat × Nat)) →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) n 0x1107c4 63

def yFinalZeroBytes : List UInt8 :=
  [0x44, 0x89, 0xf1, 0x44, 0x89, 0x74, 0x24, 0xc, 0x88, 0x8c, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x78, 0x2, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x70, 0x2, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x68, 0x2, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x60, 0x2, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

def yFinalZeroEffect (s : RamState) : Effect :=
  { rip := 0x110803
    writes := [⟨(.mem (stackPtr s + 12) : Operand 32), (Operand.reg 14 : Operand 32).read s⟩,
      ⟨(.mem (stackPtr s + 128) : Operand 8), (Operand.reg 14 : Operand 8).read s⟩,
      ⟨(.mem (stackPtr s + 608) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 616) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 624) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 632) : Operand 64), 0⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.reg 14 : Operand 64).read s).setWidth 32 |>.setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem y_final_zero_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary YFinalZeroPre (codeRange 0x1107c4 yFinalZeroBytes)
      yFinalZeroEffect := by
  have low (s : RamState) (r : BitVec 5) :
      ((Operand.reg r : Operand 32).read s).setWidth 8 =
        (Operand.reg r : Operand 8).read s := by
    simp only [Operand.read_reg32, Operand.read_reg8]
    exact BitVec.setWidth_setWidth_of_le _ (by decide)
  advance_begin (show StepEffect _ _ (movR32R32Effect 0x1107c4 3 1 14) from
    mov_r32_r32_rex_effect_step 0x1107c4 0x44 0xf1 (by simp [RexNoWPrefix]) rfl)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x107c7 (by decide))
  advance_then (show StepEffect _ _ (movM32R32Effect 0x1107c7 14 (.sib 4 none 0 (.d8 12))) from
    P256.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any 0x1107c7 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1107c4 yFinalZeroBytes 3 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 12 4 (by simp)
    · x86_norm
      exact (hP.codeApart 12 4 (by simp)).sub 3 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 12 4 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x107cc (by decide))
  advance_then (mov_m8_r8_legacy_effect_step 0x1107cc 1 (by decide) (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1107c4 yFinalZeroBytes 8 7
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.byteWritable
    · x86_norm
      exact (hP.codeApart 128 1 (by simp)).sub 8 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 128 1 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x107d3 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1107d3 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 632)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1107c4 yFinalZeroBytes 15 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 632 8 (by simp)
    · x86_norm
      exact (hP.codeApart 632 8 (by simp)).sub 15 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 632 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x107df (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1107df 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 624)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1107c4 yFinalZeroBytes 27 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 624 8 (by simp)
    · x86_norm
      exact (hP.codeApart 624 8 (by simp)).sub 27 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 624 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x107eb (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1107eb 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 616)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1107c4 yFinalZeroBytes 39 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 616 8 (by simp)
    · x86_norm
      exact (hP.codeApart 616 8 (by simp)).sub 39 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 616 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x107f7 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1107f7 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 608)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1107c4 yFinalZeroBytes 51 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 608 8 (by simp)
    · x86_norm
      exact (hP.codeApart 608 8 (by simp)).sub 51 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 608 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10803 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [yFinalZeroEffect, low, BitVec.setWidth_setWidth_of_le,
      gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
      Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]
    all_goals repeat first | constructor | rfl
  · x86_norm [yFinalZeroEffect, low, BitVec.setWidth_setWidth_of_le]
    all_goals repeat first | constructor | rfl
  · intro f; cases f <;> x86_norm [yFinalZeroEffect, low, BitVec.setWidth_setWidth_of_le]
    all_goals repeat first | constructor | rfl
  · x86_norm [yFinalZeroEffect, low, BitVec.setWidth_setWidth_of_le]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks
