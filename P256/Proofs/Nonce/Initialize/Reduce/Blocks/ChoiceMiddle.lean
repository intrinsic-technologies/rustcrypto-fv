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

def choiceMiddleBytes : List UInt8 :=
  [0x31, 0xc9, 0x48, 0x2b, 0x4c, 0x24, 0x48, 0x48, 0xc1, 0xf9, 0x3f, 0x4c, 0x1, 0xc1, 0x48, 0x21, 0xd1, 0x48, 0x9, 0xf9, 0x48, 0xc1, 0xe9, 0x3f, 0x48, 0x89, 0x4c, 0x24, 0x48, 0x31, 0xc9, 0x48, 0x2b, 0x4c, 0x24, 0x48, 0x48, 0xc1, 0xf9, 0x3f, 0x4c, 0x1, 0xd9, 0x4c, 0x21, 0xc9, 0x48, 0x9, 0xf1, 0x48, 0xc1, 0xe9, 0x3f, 0x48, 0x89, 0x4c, 0x24, 0x48]

def choiceMiddleEffect (s : RamState) : Effect :=
  let v0 := (0 : BitVec 64)
  let v1 := (v0) - ((Operand.mem (stackPtr s + 72) : Operand 64).read s)
  let v2 := (v1).sshiftRight 63
  let v3 := (v2) + ((Operand.reg 8 : Operand 64).read s)
  let v4 := (v3) &&& ((Operand.reg 2 : Operand 64).read s)
  let v5 := (v4) ||| ((Operand.reg 7 : Operand 64).read s)
  let v6 := (v5) >>> 63
  let v7 := v6
  let v8 := (0 : BitVec 64)
  let v9 := (v8) - (v7)
  let v10 := (v9).sshiftRight 63
  let v11 := (v10) + ((Operand.reg 11 : Operand 64).read s)
  let v12 := (v11) &&& ((Operand.reg 9 : Operand 64).read s)
  let v13 := (v12) ||| ((Operand.reg 6 : Operand 64).read s)
  let v14 := (v13) >>> 63
  let v15 := v14
  { rip := 0x107b18
    writes := [⟨(.reg 1 : Operand 64), v14⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 64), v15⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem choiceMiddle_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x107ade) (codeRange 0x107ade choiceMiddleBytes)
      (Effect.post choiceMiddleEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (xor_r32_r32_effect_step 0x107ade 0xc9 rfl)))
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x7ae0 (by decide))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_m64_effect_step 0x107ae0 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 2 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7ae5 (by decide))⟩
    x86_norm
    exact (hP.writable 72 (by decide) (by decide)).readable
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sar_r64_imm8_effect_step 0x107ae5 0x48 0xf9 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 7 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7ae9 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (add_r64_r64_effect_step 0x107ae9 0x4c 0xc1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7aec (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x107aec 0x48 0xd1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7aef (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x107aef 0x48 0xf9 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 17 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7af2 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x107af2 0x48 0xe9 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 20 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7af6 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x107af6 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 24 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x7afb (by decide))⟩
    · x86_norm
      exact hP.writable 72 (by decide) (by decide)
    · x86_norm
      exact hP.apart 72 8 (by decide) 0x7af6 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 72 8 (by decide) 0x7ade 58 (by decide)
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (xor_r32_r32_effect_step 0x107afb 0xc9 rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 29 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7afd (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_m64_effect_step 0x107afd 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 31 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b02 (by decide))⟩
    x86_norm
    exact (hP.writable 72 (by decide) (by decide)).readable
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sar_r64_imm8_effect_step 0x107b02 0x48 0xf9 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 36 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b06 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (add_r64_r64_effect_step 0x107b06 0x4c 0xd9 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 40 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b09 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x107b09 0x4c 0xc9 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 43 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b0c (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x107b0c 0x48 0xf1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 46 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b0f (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x107b0f 0x48 0xe9 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 49 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b13 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x107b13 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107ade choiceMiddleBytes 53 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x7b18 (by decide))⟩
    · x86_norm
      exact hP.writable 72 (by decide) (by decide)
    · x86_norm
      exact hP.apart 72 8 (by decide) 0x7b13 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 72 8 (by decide) 0x7ade 58 (by decide)
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [choiceMiddleEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp only [Int.reduceToNat, gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk,
      Fin.getElem_fin, Fin.isValue, Operand.read_reg64, Fin.val_two, gprNumber, Nat.pow_one, Nat.zero_mod,
      Nat.zero_shiftLeft, Nat.add_zero, modrmRm, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', Nat.one_mod,
      Nat.zero_add, Operand.read_reg32, Fin.mk_one, Nat.reduceAdd, Fin.val_one, modrmReg, BitVec.xor_self,
      Nat.reduceLeDiff, Nat.zero_lt_succ, BitVec.setWidth_ofNat_of_le_of_lt, BitVec.zero_sub, shiftCount, ↓reduceIte,
      Nat.mod_succ, rexR, Nat.reduceShiftLeft, and_self, or_self]
  · intro i
    cases i <;> x86_norm [choiceMiddleEffect]
  · x86_norm [choiceMiddleEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
