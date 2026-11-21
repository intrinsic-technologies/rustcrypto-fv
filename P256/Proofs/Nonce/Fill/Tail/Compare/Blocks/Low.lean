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

def lowBytes : List UInt8 :=
  [0x48, 0x8b, 0x4c, 0x24, 0x48, 0x49, 0x8b, 0x17, 0x48, 0x89, 0xce, 0x48, 0x29, 0xd6, 0x48, 0xf7, 0xd1, 0x48, 0x89, 0xd7, 0x48, 0x21, 0xcf, 0x48, 0x9, 0xd1, 0x48, 0x21, 0xf1, 0x48, 0x9, 0xf9, 0x48, 0xc1, 0xe9, 0x3f, 0x48, 0x89, 0x4c, 0x24, 0x8, 0x31, 0xc9, 0x48, 0x2b, 0x4c, 0x24, 0x8]

def lowEffect (s : RamState) : Effect :=
  let v0 := (Operand.mem (stackPtr s + 72) : Operand 64).read s
  let v1 := (Operand.mem ((Operand.reg 15 : Operand 64).read s + 0) : Operand 64).read s
  let v2 := v0
  let v3 := (v2) - (v1)
  let v4 := ~~~(v0)
  let v5 := v1
  let v6 := (v5) &&& (v4)
  let v7 := (v4) ||| (v1)
  let v8 := (v7) &&& (v3)
  let v9 := (v8) ||| (v6)
  let v10 := (v9) >>> 63
  let v11 := v10
  let v12 := (0 : BitVec 64)
  let v13 := (v12) - (v11)
  { rip := 0x107615
    writes := [⟨(.reg 1 : Operand 64), v13⟩,
      ⟨(.reg 2 : Operand 64), v1⟩,
      ⟨(.reg 6 : Operand 64), v3⟩,
      ⟨(.reg 7 : Operand 64), v6⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), v11⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem low_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x1075e5) (codeRange 0x1075e5 lowBytes)
      (Effect.post lowEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1075e5 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, (hP.writable 72 (by decide) (by decide)).readable⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x75ea (by decide))
  advance_then (mov_r64_m64_effect_step 0x1075ea 0x49 (by simp [RexWPrefix]) 2 (.base 15 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 5 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x75ed (by decide))⟩
    x86_norm
    exact hP.order 0 (by decide) (by decide)
  advance_then (mov_r64_r64_effect_step 0x1075ed 0x48 0xce (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 6, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x75f0 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_r64_effect_step 0x1075f0 0x48 0xd6 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 6, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x75f3 (by decide))⟩
  advance_then (not_r64_effect_step 0x1075f3 0x48 0xd1 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x75f6 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1075f6 0x48 0xd7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 17 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 7, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x75f9 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x1075f9 0x48 0xcf (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 20 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 7, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x75fc (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x1075fc 0x48 0xd1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 23 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x75ff (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x1075ff 0x48 0xf1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 26 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7602 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x107602 0x48 0xf9 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 29 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7605 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x107605 0x48 0xe9 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 32 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7609 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x107609 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 36 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x760e (by decide))⟩
    · x86_norm
      exact hP.writable 8 (by decide) (by decide)
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x7609 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x75e5 48 (by decide)
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (xor_r32_r32_effect_step 0x10760e 0xc9 rfl)))
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 41 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7610 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_m64_effect_step 0x107610 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x1075e5 lowBytes 43 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7615 (by decide))⟩
    x86_norm
    exact (hP.writable 8 (by decide) (by decide)).readable
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [lowEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp [Operand.read_reg64, shiftCount, gprIndex]
  · intro i
    cases i <;> x86_norm [lowEffect]
  · x86_norm [lowEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Fill.Tail.Compare.Blocks
