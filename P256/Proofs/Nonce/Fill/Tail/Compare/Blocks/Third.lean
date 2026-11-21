import P256.Proofs.Nonce.Fill.Tail.Compare.Blocks.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare.Blocks

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
  [0x48, 0x8b, 0x54, 0x24, 0x58, 0x49, 0x8b, 0x77, 0x10, 0x48, 0xc1, 0xf9, 0x3f, 0x48, 0x1, 0xd1, 0x48, 0x29, 0xf1, 0x48, 0xf7, 0xd2, 0x48, 0x89, 0xf7, 0x48, 0x21, 0xd7, 0x48, 0x9, 0xf2, 0x48, 0x21, 0xca, 0x48, 0x9, 0xfa, 0x48, 0xc1, 0xea, 0x3f, 0x48, 0x89, 0x54, 0x24, 0x8, 0x48, 0x8b, 0x4c, 0x24, 0x8, 0x31, 0xd2, 0x48, 0x29, 0xca]

def thirdEffect (s : RamState) : Effect :=
  let v0 := (Operand.mem (stackPtr s + 88) : Operand 64).read s
  let v1 := (Operand.mem ((Operand.reg 15 : Operand 64).read s + 16) : Operand 64).read s
  let v2 := ((Operand.reg 1 : Operand 64).read s).sshiftRight 63
  let v3 := (v2) + (v0)
  let v4 := (v3) - (v1)
  let v5 := ~~~(v0)
  let v6 := v1
  let v7 := (v6) &&& (v5)
  let v8 := (v5) ||| (v1)
  let v9 := (v8) &&& (v4)
  let v10 := (v9) ||| (v7)
  let v11 := (v10) >>> 63
  let v12 := v11
  let v13 := v12
  let v14 := (0 : BitVec 64)
  let v15 := (v14) - (v13)
  { rip := 0x107684
    writes := [⟨(.reg 1 : Operand 64), v13⟩,
      ⟨(.reg 2 : Operand 64), v15⟩,
      ⟨(.reg 6 : Operand 64), v1⟩,
      ⟨(.reg 7 : Operand 64), v7⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), v12⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem third_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x10764c) (codeRange 0x10764c thirdBytes)
      (Effect.post thirdEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10764c 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, (hP.writable 88 (by decide) (by decide)).readable⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x7651 (by decide))
  advance_then (mov_r64_m64_effect_step 0x107651 0x49 (by simp [RexWPrefix]) 6 (.base 15 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 5 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 6, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7655 (by decide))⟩
    x86_norm
    exact hP.order 16 (by decide) (by decide)
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sar_r64_imm8_effect_step 0x107655 0x48 0xf9 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 9 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7659 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (add_r64_r64_effect_step 0x107659 0x48 0xd1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x765c (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_r64_effect_step 0x10765c 0x48 0xf1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x765f (by decide))⟩
  advance_then (not_r64_effect_step 0x10765f 0x48 0xd2 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 19 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7662 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x107662 0x48 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 22 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 7, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7665 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x107665 0x48 0xd7 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 25 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 7, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7668 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x107668 0x48 0xf2 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 28 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x766b (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x10766b 0x48 0xca (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 31 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x766e (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x10766e 0x48 0xfa (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 34 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7671 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x107671 0x48 0xea 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 37 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7675 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x107675 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 41 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x767a (by decide))⟩
    · x86_norm
      exact hP.writable 8 (by decide) (by decide)
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x7675 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x764c 56 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10767a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 46 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x767f (by decide))⟩
    x86_norm
    exact (hP.writable 8 (by decide) (by decide)).readable
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (xor_r32_r32_effect_step 0x10767f 0xd2 rfl)))
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 51 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7681 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_r64_effect_step 0x107681 0x48 0xca (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10764c thirdBytes 53 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7684 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [thirdEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp [Operand.read_reg64, shiftCount, gprNumber, rexB, modrmRm, gprIndex]
  · intro i
    cases i <;> x86_norm [thirdEffect]
  · x86_norm [thirdEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Fill.Tail.Compare.Blocks
