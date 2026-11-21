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

def choiceHighBytes : List UInt8 :=
  [0x31, 0xc9, 0x48, 0x2b, 0x4c, 0x24, 0x48, 0x48, 0xc1, 0xf9, 0x3f, 0x4c, 0x1, 0xe9, 0x4c, 0x21, 0xf9, 0x48, 0x9, 0xe9, 0x48, 0xc1, 0xe9, 0x3f, 0x48, 0x89, 0x4c, 0x24, 0x48]

def choiceHighEffect (s : RamState) : Effect :=
  let v0 := (0 : BitVec 64)
  let v1 := (v0) - ((Operand.mem (stackPtr s + 72) : Operand 64).read s)
  let v2 := (v1).sshiftRight 63
  let v3 := (v2) + ((Operand.reg 13 : Operand 64).read s)
  let v4 := (v3) &&& ((Operand.reg 15 : Operand 64).read s)
  let v5 := (v4) ||| ((Operand.reg 5 : Operand 64).read s)
  let v6 := (v5) >>> 63
  let v7 := v6
  { rip := 0x107b35
    writes := [⟨(.reg 1 : Operand 64), v6⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 64), v7⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem choiceHigh_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x107b18) (codeRange 0x107b18 choiceHighBytes)
      (Effect.post choiceHighEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (xor_r32_r32_effect_step 0x107b18 0xc9 rfl)))
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x7b1a (by decide))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_m64_effect_step 0x107b1a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107b18 choiceHighBytes 2 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b1f (by decide))⟩
    x86_norm
    exact (hP.writable 72 (by decide) (by decide)).readable
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sar_r64_imm8_effect_step 0x107b1f 0x48 0xf9 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107b18 choiceHighBytes 7 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b23 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (add_r64_r64_effect_step 0x107b23 0x4c 0xe9 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107b18 choiceHighBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b26 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x107b26 0x4c 0xf9 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107b18 choiceHighBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b29 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x107b29 0x48 0xe9 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107b18 choiceHighBytes 17 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b2c (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x107b2c 0x48 0xe9 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107b18 choiceHighBytes 20 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b30 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x107b30 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107b18 choiceHighBytes 24 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x7b35 (by decide))⟩
    · x86_norm
      exact hP.writable 72 (by decide) (by decide)
    · x86_norm
      exact hP.apart 72 8 (by decide) 0x7b30 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 72 8 (by decide) 0x7b18 29 (by decide)
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [choiceHighEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp only [Int.reduceToNat, gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk,
      Fin.getElem_fin, Fin.isValue, Operand.read_reg64, gprNumber, Nat.pow_one, Nat.zero_mod, Nat.zero_shiftLeft,
      Nat.add_zero, modrmRm, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', Nat.one_mod, Nat.zero_add,
      Operand.read_reg32, Fin.mk_one, Nat.reduceAdd, Fin.val_one, modrmReg, BitVec.xor_self, Nat.reduceLeDiff,
      Nat.zero_lt_succ, BitVec.setWidth_ofNat_of_le_of_lt, BitVec.zero_sub, shiftCount, ↓reduceIte, Nat.mod_succ, rexR,
      Nat.reduceShiftLeft, and_self]
  · intro i
    cases i <;> x86_norm [choiceHighEffect]
  · x86_norm [choiceHighEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
