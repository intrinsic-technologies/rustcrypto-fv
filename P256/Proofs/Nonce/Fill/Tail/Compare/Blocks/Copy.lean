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

def copyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x8, 0x48, 0x8b, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x54, 0x24, 0x20, 0x48, 0x8b, 0x74, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x89, 0x4c, 0x24, 0x50, 0x48, 0x89, 0x74, 0x24, 0x58, 0x48, 0x89, 0x54, 0x24, 0x60, 0x48, 0xc7, 0x44, 0x24, 0x20, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x18, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x10, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x8, 0x0, 0x0, 0x0, 0x0, 0xbe, 0x4, 0x0, 0x0, 0x0, 0xb9, 0x4, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x7c, 0x24, 0x48, 0x4c, 0x89, 0xe2]

def copyEffect (s : RamState) : Effect :=
  let v0 := (Operand.mem (stackPtr s + 8) : Operand 64).read s
  let v1 := (Operand.mem (stackPtr s + 16) : Operand 64).read s
  let v2 := v0
  let v3 := (Operand.mem (stackPtr s + 32) : Operand 64).read s
  let v4 := (Operand.mem (stackPtr s + 24) : Operand 64).read s
  let v5 := v0
  let v6 := v1
  let v7 := v4
  let v8 := v3
  let v9 := (0x0 : BitVec 64)
  let v10 := (0x0 : BitVec 64)
  let v11 := (0x0 : BitVec 64)
  let v12 := (0x0 : BitVec 64)
  let v13 := (0x4 : BitVec 64)
  let v14 := (0x4 : BitVec 64)
  let v15 := (Operand.reg 4 : Operand 64).read s + 72
  let v16 := (Operand.reg 12 : Operand 64).read s
  { rip := 0x1075e0
    writes := [⟨(.reg 0 : Operand 64), v0⟩,
      ⟨(.reg 1 : Operand 64), v14⟩,
      ⟨(.reg 2 : Operand 64), v16⟩,
      ⟨(.reg 6 : Operand 64), v13⟩,
      ⟨(.reg 7 : Operand 64), v15⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), v12⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), v11⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), v10⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), v9⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 64), v5⟩,
      ⟨(.mem (stackPtr s + 80) : Operand 64), v6⟩,
      ⟨(.mem (stackPtr s + 88) : Operand 64), v7⟩,
      ⟨(.mem (stackPtr s + 96) : Operand 64), v8⟩,
      ⟨(.mem (stackPtr s + 152) : Operand 64), v2⟩]
 }

set_option maxHeartbeats 1600000 in
theorem copy_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x10757a) (codeRange 0x10757a copyBytes)
      (Effect.post copyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10757a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, (hP.writable 8 (by decide) (by decide)).readable⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x757f (by decide))
  advance_then (mov_r64_m64_effect_step 0x10757f 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7584 (by decide))⟩
    x86_norm
    exact (hP.writable 16 (by decide) (by decide)).readable
  advance_then (mov_m64_r64_effect_step 0x107584 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 10 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x758c (by decide))⟩
    · x86_norm
      exact hP.writable 152 (by decide) (by decide)
    · x86_norm
      exact hP.apart 152 8 (by decide) 0x7584 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 152 8 (by decide) 0x757a 102 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10758c 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 18 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7591 (by decide))⟩
    x86_norm
    exact (hP.writable 32 (by decide) (by decide)).readable
  advance_then (mov_r64_m64_effect_step 0x107591 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 23 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 6, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7596 (by decide))⟩
    x86_norm
    exact (hP.writable 24 (by decide) (by decide)).readable
  advance_then (mov_m64_r64_effect_step 0x107596 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 28 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x759b (by decide))⟩
    · x86_norm
      exact hP.writable 72 (by decide) (by decide)
    · x86_norm
      exact hP.apart 72 8 (by decide) 0x7596 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 72 8 (by decide) 0x757a 102 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10759b 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 33 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x75a0 (by decide))⟩
    · x86_norm
      exact hP.writable 80 (by decide) (by decide)
    · x86_norm
      exact hP.apart 80 8 (by decide) 0x759b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 80 8 (by decide) 0x757a 102 (by decide)
  advance_then (mov_m64_r64_effect_step 0x1075a0 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 38 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x75a5 (by decide))⟩
    · x86_norm
      exact hP.writable 88 (by decide) (by decide)
    · x86_norm
      exact hP.apart 88 8 (by decide) 0x75a0 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 88 8 (by decide) 0x757a 102 (by decide)
  advance_then (mov_m64_r64_effect_step 0x1075a5 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 43 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x75aa (by decide))⟩
    · x86_norm
      exact hP.writable 96 (by decide) (by decide)
    · x86_norm
      exact hP.apart 96 8 (by decide) 0x75a5 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 96 8 (by decide) 0x757a 102 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x1075aa 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 48 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x75b3 (by decide))⟩
    · x86_norm
      exact hP.writable 32 (by decide) (by decide)
    · x86_norm
      exact hP.apart 32 8 (by decide) 0x75aa 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 32 8 (by decide) 0x757a 102 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x1075b3 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 57 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x75bc (by decide))⟩
    · x86_norm
      exact hP.writable 24 (by decide) (by decide)
    · x86_norm
      exact hP.apart 24 8 (by decide) 0x75b3 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 8 (by decide) 0x757a 102 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x1075bc 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 66 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x75c5 (by decide))⟩
    · x86_norm
      exact hP.writable 16 (by decide) (by decide)
    · x86_norm
      exact hP.apart 16 8 (by decide) 0x75bc 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 8 (by decide) 0x757a 102 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x1075c5 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 75 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x75ce (by decide))⟩
    · x86_norm
      exact hP.writable 8 (by decide) (by decide)
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x75c5 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x757a 102 (by decide)
  advance_then (mov_r32_imm32_effect_step 0x1075ce 0xbe (by decide) 4)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 84 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 6, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x75d3 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x1075d3 0xb9 (by decide) 4)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 89 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x75d8 (by decide))⟩
  advance_then (lea_r64_effect_step 0x1075d8 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 94 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 7, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x75dd (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1075dd 0x4c 0xe2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10757a copyBytes 99 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x75e0 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [copyEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp [Operand.read_reg64, gprNumber, rexR, modrmReg, gprIndex]
  · intro i
    cases i <;> x86_norm [copyEffect]
  · x86_norm [copyEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Fill.Tail.Compare.Blocks
