import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Reduce.Blocks

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sar_r64_imm8_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

attribute [local x86_compose] andAlImm8Effect

def lowBytes : List UInt8 :=
  [0x48, 0x89, 0xc8, 0x4c, 0x29, 0xf8, 0x48, 0x89, 0x84, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x48, 0xf7, 0xd1, 0x4c, 0x89, 0xfa, 0x48, 0x21, 0xca, 0x4c, 0x9, 0xf9, 0x48, 0x21, 0xc1, 0x48, 0x9, 0xd1, 0x48, 0xc1, 0xe9, 0x3f, 0x48, 0x89, 0x4c, 0x24, 0x8, 0x48, 0x8d, 0x44, 0x24, 0x8, 0x45, 0x31, 0xd2, 0x4c, 0x2b, 0x54, 0x24, 0x8]

def lowEffect (s : RamState) : Effect :=
  let v0 := (Operand.reg 1 : Operand 64).read s
  let v1 := (v0) - ((Operand.reg 15 : Operand 64).read s)
  let v2 := v1
  let v3 := ~~~((Operand.reg 1 : Operand 64).read s)
  let v4 := (Operand.reg 15 : Operand 64).read s
  let v5 := (v4) &&& (v3)
  let v6 := (v3) ||| ((Operand.reg 15 : Operand 64).read s)
  let v7 := (v6) &&& (v1)
  let v8 := (v7) ||| (v5)
  let v9 := (v8) >>> 63
  let v10 := v9
  let v11 := (Operand.reg 4 : Operand 64).read s + 8
  let v12 := (0 : BitVec 64)
  let v13 := (v12) - (v10)
  { rip := 0x107a09
    writes := [⟨(.reg 0 : Operand 64), v11⟩,
      ⟨(.reg 1 : Operand 64), v9⟩,
      ⟨(.reg 2 : Operand 64), v5⟩,
      ⟨(.reg 10 : Operand 64), v13⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), v10⟩,
      ⟨(.mem (stackPtr s + 160) : Operand 64), v2⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem low_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x1079d3) (codeRange 0x1079d3 lowBytes)
      (Effect.post lowEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x1079d3 0x48 0xc8 (by simp [RexWPrefix]) rfl)
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x79d6 (by decide))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_r64_effect_step 0x1079d6 0x4c 0xf8 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 0, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x79d9 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x1079d9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 6 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x79e1 (by decide))⟩
    · x86_norm
      exact hP.writable 160 (by decide) (by decide)
    · x86_norm
      exact hP.apart 160 8 (by decide) 0x79d9 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 160 8 (by decide) 0x79d3 54 (by decide)
  advance_then (not_r64_effect_step 0x1079e1 0x48 0xd1 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x79e4 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1079e4 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 17 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x79e7 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x1079e7 0x48 0xca (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 20 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x79ea (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x1079ea 0x4c 0xf9 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 23 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x79ed (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x1079ed 0x48 0xc1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 26 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x79f0 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x1079f0 0x48 0xd1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 29 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x79f3 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x1079f3 0x48 0xe9 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 32 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x79f7 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x1079f7 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 36 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x79fc (by decide))⟩
    · x86_norm
      exact hP.writable 8 (by decide) (by decide)
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x79f7 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x79d3 54 (by decide)
  advance_then (lea_r64_effect_step 0x1079fc 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 41 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 0, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a01 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (xor_r32_r32_rex_effect_step 0x107a01 0x45 0xd2 (by simp [RexNoWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 46 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 10, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a04 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_m64_effect_step 0x107a04 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x1079d3 lowBytes 49 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 10, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a09 (by decide))⟩
    x86_norm
    exact (hP.writable 8 (by decide) (by decide)).readable
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [lowEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp only [Operand.read_reg64, Int.reduceToNat, gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.one_mod,
      Fin.mk_one, Fin.isValue, Fin.getElem_fin, Nat.reduceAdd, Fin.val_one, Nat.reduceMod, Fin.reduceFinMk, gprNumber,
      Nat.pow_one, Nat.zero_mod, Nat.zero_shiftLeft, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', Nat.add_zero,
      modrmRm, Nat.zero_add, rexR, Nat.mod_succ, Nat.reduceShiftLeft, modrmReg, shiftCount, ↓reduceIte,
      Operand.read_reg32, BitVec.xor_self, Nat.reduceLeDiff, Nat.zero_lt_succ, BitVec.setWidth_ofNat_of_le_of_lt,
      BitVec.zero_sub, BitVec.add_right_inj, BitVec.reduceEq, false_and, and_self, or_true, or_false]
  · intro i
    cases i <;> x86_norm [lowEffect]
  · x86_norm [lowEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
