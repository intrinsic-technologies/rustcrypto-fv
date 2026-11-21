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

def thirdBytes : List UInt8 :=
  [0x4c, 0x8b, 0x4c, 0x24, 0x78, 0x4d, 0x89, 0xcb, 0x4d, 0x29, 0xeb, 0x49, 0xc1, 0xfc, 0x3f, 0x4d, 0x1, 0xdc, 0x49, 0xf7, 0xd1, 0x4c, 0x89, 0xee, 0x4c, 0x21, 0xce, 0x4d, 0x9, 0xe9, 0x4d, 0x89, 0xe7, 0x4d, 0x21, 0xcf, 0x49, 0x9, 0xf7, 0x49, 0xc1, 0xef, 0x3f, 0x4c, 0x89, 0x7c, 0x24, 0x8]

def thirdEffect (s : RamState) : Effect :=
  let v0 := (Operand.mem (stackPtr s + 120) : Operand 64).read s
  let v1 := v0
  let v2 := (v1) - ((Operand.reg 13 : Operand 64).read s)
  let v3 := ((Operand.reg 12 : Operand 64).read s).sshiftRight 63
  let v4 := (v3) + (v2)
  let v5 := ~~~(v0)
  let v6 := (Operand.reg 13 : Operand 64).read s
  let v7 := (v6) &&& (v5)
  let v8 := (v5) ||| ((Operand.reg 13 : Operand 64).read s)
  let v9 := v4
  let v10 := (v9) &&& (v8)
  let v11 := (v10) ||| (v7)
  let v12 := (v11) >>> 63
  let v13 := v12
  { rip := 0x107a71
    writes := [⟨(.reg 6 : Operand 64), v7⟩,
      ⟨(.reg 9 : Operand 64), v8⟩,
      ⟨(.reg 11 : Operand 64), v2⟩,
      ⟨(.reg 12 : Operand 64), v4⟩,
      ⟨(.reg 15 : Operand 64), v12⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), v13⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem third_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x107a41) (codeRange 0x107a41 thirdBytes)
      (Effect.post thirdEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x107a41 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, (hP.writable 120 (by decide) (by decide)).readable⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x7a46 (by decide))
  advance_then (mov_r64_r64_effect_step 0x107a46 0x4d 0xcb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 11, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a49 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_r64_effect_step 0x107a49 0x4d 0xeb (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 11, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a4c (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sar_r64_imm8_effect_step 0x107a4c 0x49 0xfc 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 11 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 12, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a50 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (add_r64_r64_effect_step 0x107a50 0x4d 0xdc (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 12, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a53 (by decide))⟩
  advance_then (not_r64_effect_step 0x107a53 0x49 0xd1 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 18 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 9, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a56 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x107a56 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 21 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 6, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a59 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x107a59 0x4c 0xce (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 24 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 6, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a5c (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x107a5c 0x4d 0xe9 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 27 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 9, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a5f (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x107a5f 0x4d 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 30 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 15, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a62 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x107a62 0x4d 0xcf (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 33 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 15, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a65 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x107a65 0x49 0xf7 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 36 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 15, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a68 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x107a68 0x49 0xef 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 39 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 15, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a6c (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x107a6c 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107a41 thirdBytes 43 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x7a71 (by decide))⟩
    · x86_norm
      exact hP.writable 8 (by decide) (by decide)
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x7a6c 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x7a41 48 (by decide)
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [thirdEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp only [Operand.read_reg64, Int.reduceToNat, gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Fin.reduceFinMk, Fin.getElem_fin, Fin.isValue, gprNumber, Nat.pow_one, Nat.zero_mod, Nat.zero_shiftLeft, rexR,
      UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', Nat.mod_succ, Nat.zero_add, Nat.one_mod, Nat.reduceShiftLeft,
      modrmReg, Nat.reduceAdd, rexB, modrmRm, shiftCount, ↓reduceIte, and_self]
  · intro i
    cases i <;> x86_norm [thirdEffect]
  · x86_norm [thirdEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
