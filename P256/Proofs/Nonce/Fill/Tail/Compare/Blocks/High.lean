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

def highBytes : List UInt8 :=
  [0x48, 0x8b, 0x4c, 0x24, 0x60, 0x49, 0x8b, 0x77, 0x18, 0x48, 0xc1, 0xfa, 0x3f, 0x48, 0x1, 0xca, 0x48, 0x29, 0xf2, 0x48, 0xf7, 0xd1, 0x48, 0x89, 0xf7, 0x48, 0x21, 0xcf, 0x48, 0x9, 0xf1, 0x48, 0x21, 0xd1, 0x48, 0x9, 0xf9, 0x48, 0xc1, 0xe9, 0x3f, 0x48, 0x89, 0x4c, 0x24, 0x8]

def highEffect (s : RamState) : Effect :=
  let v0 := (Operand.mem (stackPtr s + 96) : Operand 64).read s
  let v1 := (Operand.mem ((Operand.reg 15 : Operand 64).read s + 24) : Operand 64).read s
  let v2 := ((Operand.reg 2 : Operand 64).read s).sshiftRight 63
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
  { rip := 0x1076b2
    writes := [⟨(.reg 1 : Operand 64), v11⟩,
      ⟨(.reg 2 : Operand 64), v4⟩,
      ⟨(.reg 6 : Operand 64), v1⟩,
      ⟨(.reg 7 : Operand 64), v7⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), v12⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem high_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x107684) (codeRange 0x107684 highBytes)
      (Effect.post highEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x107684 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, (hP.writable 96 (by decide) (by decide)).readable⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x7689 (by decide))
  advance_then (mov_r64_m64_effect_step 0x107689 0x49 (by simp [RexWPrefix]) 6 (.base 15 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107684 highBytes 5 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 6, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x768d (by decide))⟩
    x86_norm
    exact hP.order 24 (by decide) (by decide)
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sar_r64_imm8_effect_step 0x10768d 0x48 0xfa 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107684 highBytes 9 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7691 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (add_r64_r64_effect_step 0x107691 0x48 0xca (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107684 highBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7694 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_r64_effect_step 0x107694 0x48 0xf2 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107684 highBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7697 (by decide))⟩
  advance_then (not_r64_effect_step 0x107697 0x48 0xd1 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107684 highBytes 19 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x769a (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10769a 0x48 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107684 highBytes 22 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 7, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x769d (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x10769d 0x48 0xcf (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107684 highBytes 25 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 7, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x76a0 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x1076a0 0x48 0xf1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107684 highBytes 28 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x76a3 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x1076a3 0x48 0xd1 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107684 highBytes 31 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x76a6 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x1076a6 0x48 0xf9 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107684 highBytes 34 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x76a9 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x1076a9 0x48 0xe9 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107684 highBytes 37 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x76ad (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x1076ad 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107684 highBytes 41 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x76b2 (by decide))⟩
    · x86_norm
      exact hP.writable 8 (by decide) (by decide)
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x76ad 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x7684 46 (by decide)
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [highEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp [Operand.read_reg64, shiftCount, gprNumber, rexB, modrmRm, gprIndex]
  · intro i
    cases i <;> x86_norm [highEffect]
  · x86_norm [highEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Fill.Tail.Compare.Blocks
