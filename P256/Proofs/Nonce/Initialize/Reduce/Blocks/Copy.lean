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

def copyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8b, 0x4c, 0x24, 0x8, 0x48, 0x8b, 0x54, 0x24, 0x10, 0x48, 0x89, 0x4c, 0x24, 0x48, 0x48, 0x8b, 0x74, 0x24, 0x18, 0x48, 0x89, 0x4c, 0x24, 0x68, 0x48, 0x89, 0x54, 0x24, 0x70, 0x48, 0x89, 0x74, 0x24, 0x78, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0]

def copyEffect (s : RamState) : Effect :=
  let v0 := (Operand.mem (stackPtr s + 32) : Operand 64).read s
  let v1 := v0
  let v2 := (Operand.mem (stackPtr s + 8) : Operand 64).read s
  let v3 := (Operand.mem (stackPtr s + 16) : Operand 64).read s
  let v4 := v2
  let v5 := (Operand.mem (stackPtr s + 24) : Operand 64).read s
  let v6 := v2
  let v7 := v3
  let v8 := v5
  let v9 := v0
  { rip := 0x1079d3
    writes := [⟨(.reg 0 : Operand 64), v0⟩,
      ⟨(.reg 1 : Operand 64), v2⟩,
      ⟨(.reg 2 : Operand 64), v3⟩,
      ⟨(.reg 6 : Operand 64), v5⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 64), v4⟩,
      ⟨(.mem (stackPtr s + 96) : Operand 64), v1⟩,
      ⟨(.mem (stackPtr s + 104) : Operand 64), v6⟩,
      ⟨(.mem (stackPtr s + 112) : Operand 64), v7⟩,
      ⟨(.mem (stackPtr s + 120) : Operand 64), v8⟩,
      ⟨(.mem (stackPtr s + 128) : Operand 64), v9⟩]
 }

set_option maxHeartbeats 1600000 in
theorem copy_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x10799e) (codeRange 0x10799e copyBytes)
      (Effect.post copyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10799e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, (hP.writable 32 (by decide) (by decide)).readable⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x79a3 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1079a3 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10799e copyBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x79a8 (by decide))⟩
    · x86_norm
      exact hP.writable 96 (by decide) (by decide)
    · x86_norm
      exact hP.apart 96 8 (by decide) 0x79a3 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 96 8 (by decide) 0x799e 53 (by decide)
  advance_then (mov_r64_m64_effect_step 0x1079a8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10799e copyBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x79ad (by decide))⟩
    x86_norm
    exact (hP.writable 8 (by decide) (by decide)).readable
  advance_then (mov_r64_m64_effect_step 0x1079ad 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10799e copyBytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x79b2 (by decide))⟩
    x86_norm
    exact (hP.writable 16 (by decide) (by decide)).readable
  advance_then (mov_m64_r64_effect_step 0x1079b2 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10799e copyBytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x79b7 (by decide))⟩
    · x86_norm
      exact hP.writable 72 (by decide) (by decide)
    · x86_norm
      exact hP.apart 72 8 (by decide) 0x79b2 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 72 8 (by decide) 0x799e 53 (by decide)
  advance_then (mov_r64_m64_effect_step 0x1079b7 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10799e copyBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 6, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x79bc (by decide))⟩
    x86_norm
    exact (hP.writable 24 (by decide) (by decide)).readable
  advance_then (mov_m64_r64_effect_step 0x1079bc 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10799e copyBytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x79c1 (by decide))⟩
    · x86_norm
      exact hP.writable 104 (by decide) (by decide)
    · x86_norm
      exact hP.apart 104 8 (by decide) 0x79bc 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 104 8 (by decide) 0x799e 53 (by decide)
  advance_then (mov_m64_r64_effect_step 0x1079c1 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10799e copyBytes 35 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x79c6 (by decide))⟩
    · x86_norm
      exact hP.writable 112 (by decide) (by decide)
    · x86_norm
      exact hP.apart 112 8 (by decide) 0x79c1 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 112 8 (by decide) 0x799e 53 (by decide)
  advance_then (mov_m64_r64_effect_step 0x1079c6 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10799e copyBytes 40 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x79cb (by decide))⟩
    · x86_norm
      exact hP.writable 120 (by decide) (by decide)
    · x86_norm
      exact hP.apart 120 8 (by decide) 0x79c6 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 120 8 (by decide) 0x799e 53 (by decide)
  advance_then (mov_m64_r64_effect_step 0x1079cb 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10799e copyBytes 45 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x79d3 (by decide))⟩
    · x86_norm
      exact hP.writable 128 (by decide) (by decide)
    · x86_norm
      exact hP.apart 128 8 (by decide) 0x79cb 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 128 8 (by decide) 0x799e 53 (by decide)
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [copyEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp [Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [copyEffect]
  · x86_norm [copyEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
