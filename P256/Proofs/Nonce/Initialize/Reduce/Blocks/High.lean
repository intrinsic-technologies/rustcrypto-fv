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

def highBytes : List UInt8 :=
  [0x4c, 0x8b, 0xbc, 0x24, 0x80, 0x0, 0x0, 0x0, 0x4d, 0x89, 0xfd, 0x49, 0x29, 0xdd, 0x49, 0xf7, 0xd7, 0x48, 0x89, 0xdd, 0x4c, 0x21, 0xfd, 0x49, 0x9, 0xdf, 0x31, 0xc0, 0x48, 0x2b, 0x44, 0x24, 0x8, 0x48, 0xc1, 0xf8, 0x3f, 0x4c, 0x1, 0xe8, 0x4c, 0x8b, 0xb4, 0x24, 0xc0, 0x0, 0x0, 0x0, 0x48, 0x89, 0xc3, 0x4c, 0x21, 0xfb, 0x48, 0x9, 0xeb, 0x48, 0xc1, 0xeb, 0x3f, 0x48, 0x89, 0x5c, 0x24, 0x8, 0x48, 0x8d, 0x5c, 0x24, 0x8]

def highEffect (s : RamState) : Effect :=
  let v0 := (Operand.mem (stackPtr s + 128) : Operand 64).read s
  let v1 := v0
  let v2 := (v1) - ((Operand.reg 3 : Operand 64).read s)
  let v3 := ~~~(v0)
  let v4 := (Operand.reg 3 : Operand 64).read s
  let v5 := (v4) &&& (v3)
  let v6 := (v3) ||| ((Operand.reg 3 : Operand 64).read s)
  let v7 := (0 : BitVec 64)
  let v8 := (v7) - ((Operand.mem (stackPtr s + 8) : Operand 64).read s)
  let v9 := (v8).sshiftRight 63
  let v10 := (v9) + (v2)
  let v11 := (Operand.mem (stackPtr s + 192) : Operand 64).read s
  let v12 := v10
  let v13 := (v12) &&& (v6)
  let v14 := (v13) ||| (v5)
  let v15 := (v14) >>> 63
  let v16 := v15
  let v17 := (Operand.reg 4 : Operand 64).read s + 8
  { rip := 0x107ab8
    writes := [⟨(.reg 0 : Operand 64), v10⟩,
      ⟨(.reg 3 : Operand 64), v17⟩,
      ⟨(.reg 5 : Operand 64), v5⟩,
      ⟨(.reg 13 : Operand 64), v2⟩,
      ⟨(.reg 14 : Operand 64), v11⟩,
      ⟨(.reg 15 : Operand 64), v6⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), v16⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem high_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x107a71) (codeRange 0x107a71 highBytes)
      (Effect.post highEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x107a71 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, (hP.writable 128 (by decide) (by decide)).readable⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x7a79 (by decide))
  advance_then (mov_r64_r64_effect_step 0x107a79 0x4d 0xfd (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 13, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a7c (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_r64_effect_step 0x107a7c 0x49 0xdd (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 13, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a7f (by decide))⟩
  advance_then (not_r64_effect_step 0x107a7f 0x49 0xd7 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 15, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a82 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x107a82 0x48 0xdd (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 17 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 5, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a85 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x107a85 0x4c 0xfd (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 20 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 5, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a88 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x107a88 0x49 0xdf (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 23 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 15, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a8b (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (xor_r32_r32_effect_step 0x107a8b 0xc0 rfl)))
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 26 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 0, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a8d (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sub_r64_m64_effect_step 0x107a8d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 28 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 0, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a92 (by decide))⟩
    x86_norm
    exact (hP.writable 8 (by decide) (by decide)).readable
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (sar_r64_imm8_effect_step 0x107a92 0x48 0xf8 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 33 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 0, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a96 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (add_r64_r64_effect_step 0x107a96 0x4c 0xe8 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 37 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 0, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7a99 (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x107a99 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 14, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7aa1 (by decide))⟩
    x86_norm
    exact (hP.writable 192 (by decide) (by decide)).readable
  advance_then (mov_r64_r64_effect_step 0x107aa1 0x48 0xc3 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 48 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 3, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7aa4 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_r64_r64_effect_step 0x107aa4 0x4c 0xfb (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 51 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 3, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7aa7 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (or_r64_r64_effect_step 0x107aa7 0x48 0xeb (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 54 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 3, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7aaa (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (shr_r64_imm8_effect_step 0x107aaa 0x48 0xeb 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 57 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 3, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7aae (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x107aae 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 61 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x7ab3 (by decide))⟩
    · x86_norm
      exact hP.writable 8 (by decide) (by decide)
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x7aae 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x7a71 71 (by decide)
  advance_then (lea_r64_effect_step 0x107ab3 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107a71 highBytes 66 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 3, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7ab8 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [highEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp only [Int.reduceToNat, gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk,
      Fin.getElem_fin, Fin.isValue, Operand.read_reg64, gprNumber, Nat.pow_one, Nat.zero_mod, Nat.zero_shiftLeft,
      Nat.add_zero, modrmRm, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', Operand.read_reg32, Fin.zero_eta,
      Nat.reduceAdd, Fin.val_zero, modrmReg, BitVec.xor_self, Nat.reduceLeDiff, Nat.zero_lt_succ,
      BitVec.setWidth_ofNat_of_le_of_lt, BitVec.zero_sub, shiftCount, ↓reduceIte, Nat.mod_succ, rexR, Nat.zero_add,
      and_self]
  · intro i
    cases i <;> x86_norm [highEffect]
  · x86_norm [highEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
