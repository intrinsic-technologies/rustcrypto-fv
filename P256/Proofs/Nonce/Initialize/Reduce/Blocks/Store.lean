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

def storeBytes : List UInt8 :=
  [0x48, 0x8b, 0x9c, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x5c, 0x24, 0x8, 0x4c, 0x89, 0x54, 0x24, 0x10, 0x4c, 0x89, 0x64, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0x4c, 0x24, 0x48, 0x48, 0x8d, 0x44, 0x24, 0x48]

def storeEffect (s : RamState) : Effect :=
  let v0 := (Operand.mem (stackPtr s + 160) : Operand 64).read s
  let v1 := v0
  let v2 := (Operand.reg 10 : Operand 64).read s
  let v3 := (Operand.reg 12 : Operand 64).read s
  let v4 := (Operand.reg 0 : Operand 64).read s
  let v5 := (Operand.reg 1 : Operand 64).read s
  let v6 := (Operand.reg 4 : Operand 64).read s + 72
  { rip := 0x107ade
    writes := [⟨(.reg 0 : Operand 64), v6⟩,
      ⟨(.reg 3 : Operand 64), v0⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), v1⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), v2⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), v3⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), v4⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 64), v5⟩]
 }

set_option maxHeartbeats 1600000 in
theorem store_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x107ab8) (codeRange 0x107ab8 storeBytes)
      (Effect.post storeEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x107ab8 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, (hP.writable 160 (by decide) (by decide)).readable⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x7ac0 (by decide))
  advance_then (mov_m64_r64_effect_step 0x107ac0 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107ab8 storeBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x7ac5 (by decide))⟩
    · x86_norm
      exact hP.writable 8 (by decide) (by decide)
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x7ac0 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x7ab8 38 (by decide)
  advance_then (mov_m64_r64_effect_step 0x107ac5 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107ab8 storeBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x7aca (by decide))⟩
    · x86_norm
      exact hP.writable 16 (by decide) (by decide)
    · x86_norm
      exact hP.apart 16 8 (by decide) 0x7ac5 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 8 (by decide) 0x7ab8 38 (by decide)
  advance_then (mov_m64_r64_effect_step 0x107aca 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107ab8 storeBytes 18 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x7acf (by decide))⟩
    · x86_norm
      exact hP.writable 24 (by decide) (by decide)
    · x86_norm
      exact hP.apart 24 8 (by decide) 0x7aca 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 8 (by decide) 0x7ab8 38 (by decide)
  advance_then (mov_m64_r64_effect_step 0x107acf 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107ab8 storeBytes 23 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x7ad4 (by decide))⟩
    · x86_norm
      exact hP.writable 32 (by decide) (by decide)
    · x86_norm
      exact hP.apart 32 8 (by decide) 0x7acf 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 32 8 (by decide) 0x7ab8 38 (by decide)
  advance_then (mov_m64_r64_effect_step 0x107ad4 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107ab8 storeBytes 28 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0x7ad9 (by decide))⟩
    · x86_norm
      exact hP.writable 72 (by decide) (by decide)
    · x86_norm
      exact hP.apart 72 8 (by decide) 0x7ad4 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 72 8 (by decide) 0x7ab8 38 (by decide)
  advance_then (lea_r64_effect_step 0x107ad9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107ab8 storeBytes 33 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 0, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7ade (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [storeEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp only [Int.reduceToNat, gprIndex, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fin.reduceFinMk,
      Fin.getElem_fin, Fin.isValue, Operand.read_reg64, and_self, BitVec.add_right_inj, BitVec.reduceEq, gprNumber,
      Nat.pow_one, Nat.zero_mod, Nat.zero_shiftLeft, rexR, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', Nat.mod_succ,
      Nat.zero_add, Nat.one_mod, Nat.reduceShiftLeft, Nat.reduceAdd, false_and, Nat.add_zero, Fin.zero_eta, Fin.val_zero,
      Fin.mk_one, Fin.val_one, or_self, or_false, or_true]
  · intro i
    cases i <;> x86_norm [storeEffect]
  · x86_norm [storeEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
