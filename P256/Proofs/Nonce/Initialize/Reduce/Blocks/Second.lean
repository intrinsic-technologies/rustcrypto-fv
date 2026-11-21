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

def secondBytes : List UInt8 :=
  [0x48, 0x8b, 0x54, 0x24, 0x70, 0x49, 0x89, 0xd0, 0x4d, 0x29, 0xf0, 0x49, 0xc1, 0xfa, 0x3f, 0x4d, 0x1, 0xc2, 0x48, 0xf7, 0xd2, 0x4c, 0x89, 0xf7, 0x48, 0x21, 0xd7, 0x4c, 0x9, 0xf2, 0x4d, 0x89, 0xd1, 0x49, 0x21, 0xd1, 0x49, 0x9, 0xf9, 0x49, 0xc1, 0xe9, 0x3f, 0x4c, 0x89, 0x4c, 0x24, 0x8, 0x45, 0x31, 0xe4, 0x4c, 0x2b, 0x64, 0x24, 0x8]

def secondEffect (s : RamState) : Effect :=
  let v0 := (Operand.mem (stackPtr s + 112) : Operand 64).read s
  let v1 := v0
  let v2 := (v1) - ((Operand.reg 14 : Operand 64).read s)
  let v3 := ((Operand.reg 10 : Operand 64).read s).sshiftRight 63
  let v4 := (v3) + (v2)
  let v5 := ~~~(v0)
  let v6 := (Operand.reg 14 : Operand 64).read s
  let v7 := (v6) &&& (v5)
  let v8 := (v5) ||| ((Operand.reg 14 : Operand 64).read s)
  let v9 := v4
  let v10 := (v9) &&& (v8)
  let v11 := (v10) ||| (v7)
  let v12 := (v11) >>> 63
  let v13 := v12
  let v14 := (0 : BitVec 64)
  let v15 := (v14) - (v13)
  { rip := 0x107a41
    writes := [⟨(.reg 2 : Operand 64), v8⟩,
      ⟨(.reg 7 : Operand 64), v7⟩,
      ⟨(.reg 8 : Operand 64), v2⟩,
      ⟨(.reg 9 : Operand 64), v12⟩,
      ⟨(.reg 10 : Operand 64), v4⟩,
      ⟨(.reg 12 : Operand 64), v15⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), v13⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem second_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x107a09) (codeRange 0x107a09 secondBytes)
      (Effect.post secondEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x107a09 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, (hP.writable 112 (by decide) (by decide)).readable⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x7a0e (by decide))
  advance_then (mov_r64_r64_effect_step 0x107a0e 0x49 0xd0 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 8, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a11 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_r64_effect_step 0x107a11 0x4d 0xf0 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 8, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a14 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sar_r64_imm8_effect_step 0x107a14 0x49 0xfa 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 11 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 10, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a18 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (add_r64_r64_effect_step 0x107a18 0x4d 0xc2 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 10, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a1b (by decide))⟩
  advance_then (not_r64_effect_step 0x107a1b 0x48 0xd2 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 18 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a1e (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x107a1e 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 21 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 7, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a21 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x107a21 0x48 0xd7 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 24 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 7, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a24 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x107a24 0x4c 0xf2 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 27 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a27 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x107a27 0x4d 0xd1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 30 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 9, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a2a (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x107a2a 0x49 0xd1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 33 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 9, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a2d (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x107a2d 0x49 0xf9 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 36 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 9, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a30 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x107a30 0x49 0xe9 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 39 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 9, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a34 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x107a34 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 43 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x7a39 (by decide))⟩
    · x86_norm
      exact hP.writable 8 (by decide) (by decide)
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x7a34 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x7a09 56 (by decide)
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (xor_r32_r32_rex_effect_step 0x107a39 0x45 0xe4 (by simp [RexNoWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 48 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 12, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a3c (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_m64_effect_step 0x107a3c 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107a09 secondBytes 51 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 12, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a41 (by decide))⟩
    x86_norm
    exact (hP.writable 8 (by decide) (by decide)).readable
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [secondEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp only [Int.reduceToNat, gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk,
      Fin.getElem_fin, Fin.isValue, Operand.read_reg64, gprNumber, Nat.pow_one, Nat.zero_mod, Nat.zero_shiftLeft, rexR,
      UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', Nat.mod_succ, Nat.zero_add, Nat.one_mod, Nat.reduceShiftLeft,
      modrmReg, Nat.reduceAdd, rexB, modrmRm, shiftCount, ↓reduceIte, Operand.read_reg32, BitVec.xor_self,
      Nat.reduceLeDiff, Nat.zero_lt_succ, BitVec.setWidth_ofNat_of_le_of_lt, BitVec.zero_sub, and_self]
  · intro i
    cases i <;> x86_norm [secondEffect]
  · x86_norm [secondEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
