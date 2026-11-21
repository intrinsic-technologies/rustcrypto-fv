import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare.Key.Setup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a911
  writable : ∀ offset : Nat, offset + 8 ≤ 440 → offset % 8 = 0 →
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8
  readable : ∀ offset : Nat, offset + 8 ≤ 32 →
    MemReadable s (s.regValue .rdi + BitVec.ofNat 64 offset) 8
  separate : ∀ offset : Nat, offset + 8 ≤ 440 → ∀ j : Nat, j + 8 ≤ 32 →
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) 8 (s.regValue .rdi + BitVec.ofNat 64 j) 8
  apart : ∀ offset len : Nat, offset + len ≤ 440 → ∀ codeOffset codeLen : Nat,
    codeOffset + codeLen ≤ 118431 → RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen

def bytes : List UInt8 :=
  [0x48, 0x89, 0xfb, 0x48, 0xc7, 0x84, 0x24, 0x48, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x40, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x38, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x30, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x47, 0x18, 0x48, 0x8b, 0x4f, 0x10, 0x48, 0x8b, 0x17, 0x48, 0x8b, 0x77, 0x8, 0x48, 0x89, 0x54, 0x24, 0x8, 0x48, 0x89, 0x74, 0x24, 0x10, 0x48, 0x89, 0x4c, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0xc7, 0x44, 0x24, 0x28, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x30, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x38, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x40, 0x0, 0x0, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  let v0 := (Operand.reg 7 : Operand 64).read s
  let v1 := (0x0 : BitVec 64)
  let v2 := (0x0 : BitVec 64)
  let v3 := (0x0 : BitVec 64)
  let v4 := (0x0 : BitVec 64)
  let v5 := (Operand.mem ((Operand.reg 7 : Operand 64).read s + 24) : Operand 64).read s
  let v6 := (Operand.mem ((Operand.reg 7 : Operand 64).read s + 16) : Operand 64).read s
  let v7 := (Operand.mem ((Operand.reg 7 : Operand 64).read s + 0) : Operand 64).read s
  let v8 := (Operand.mem ((Operand.reg 7 : Operand 64).read s + 8) : Operand 64).read s
  let v9 := v7
  let v10 := v8
  let v11 := v6
  let v12 := v5
  let v13 := (0x0 : BitVec 64)
  let v14 := (0x0 : BitVec 64)
  let v15 := (0x0 : BitVec 64)
  let v16 := (0x0 : BitVec 64)
  { rip := 0x10a98b
    writes := [⟨(.reg 0 : Operand 64), v5⟩,
      ⟨(.reg 1 : Operand 64), v6⟩,
      ⟨(.reg 2 : Operand 64), v7⟩,
      ⟨(.reg 3 : Operand 64), v0⟩,
      ⟨(.reg 6 : Operand 64), v8⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), v9⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), v10⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), v11⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), v12⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), v13⟩,
      ⟨(.mem (stackPtr s + 48) : Operand 64), v14⟩,
      ⟨(.mem (stackPtr s + 56) : Operand 64), v15⟩,
      ⟨(.mem (stackPtr s + 64) : Operand 64), v16⟩,
      ⟨(.mem (stackPtr s + 304) : Operand 64), v4⟩,
      ⟨(.mem (stackPtr s + 312) : Operand 64), v3⟩,
      ⟨(.mem (stackPtr s + 320) : Operand 64), v2⟩,
      ⟨(.mem (stackPtr s + 328) : Operand 64), v1⟩]
 }

set_option maxHeartbeats 1600000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a911 bytes)
      (Effect.post effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10a911 0x48 0xfb (by simp [RexWPrefix]) rfl)
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0xa914 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10a914 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 3 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa920 (by decide))⟩
    · x86_norm
      exact hP.writable 328 (by decide) (by decide)
    · x86_norm
      exact hP.apart 328 8 (by decide) 0xa914 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 328 8 (by decide) 0xa911 122 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10a920 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 320)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 15 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa92c (by decide))⟩
    · x86_norm
      exact hP.writable 320 (by decide) (by decide)
    · x86_norm
      exact hP.apart 320 8 (by decide) 0xa920 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 320 8 (by decide) 0xa911 122 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10a92c 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 27 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa938 (by decide))⟩
    · x86_norm
      exact hP.writable 312 (by decide) (by decide)
    · x86_norm
      exact hP.apart 312 8 (by decide) 0xa92c 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 312 8 (by decide) 0xa911 122 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10a938 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 39 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa944 (by decide))⟩
    · x86_norm
      exact hP.writable 304 (by decide) (by decide)
    · x86_norm
      exact hP.apart 304 8 (by decide) 0xa938 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 304 8 (by decide) 0xa911 122 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10a944 0x48 (by simp [RexWPrefix]) 0 (.base 7 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 51 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 0, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0xa948 (by decide))⟩
    x86_norm
    exact hP.readable 24 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10a948 0x48 (by simp [RexWPrefix]) 1 (.base 7 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 55 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0xa94c (by decide))⟩
    x86_norm
    exact hP.readable 16 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10a94c 0x48 (by simp [RexWPrefix]) 2 (.base 7 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 59 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0xa94f (by decide))⟩
    x86_norm
    exact hP.readable 0 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10a94f 0x48 (by simp [RexWPrefix]) 6 (.base 7 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 62 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 6, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0xa953 (by decide))⟩
    x86_norm
    exact hP.readable 8 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10a953 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 66 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa958 (by decide))⟩
    · x86_norm
      exact hP.writable 8 (by decide) (by decide)
    · x86_norm
      exact hP.apart 8 8 (by decide) 0xa953 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0xa911 122 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10a958 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 71 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa95d (by decide))⟩
    · x86_norm
      exact hP.writable 16 (by decide) (by decide)
    · x86_norm
      exact hP.apart 16 8 (by decide) 0xa958 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 8 (by decide) 0xa911 122 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10a95d 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 76 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa962 (by decide))⟩
    · x86_norm
      exact hP.writable 24 (by decide) (by decide)
    · x86_norm
      exact hP.apart 24 8 (by decide) 0xa95d 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 8 (by decide) 0xa911 122 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10a962 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 81 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa967 (by decide))⟩
    · x86_norm
      exact hP.writable 32 (by decide) (by decide)
    · x86_norm
      exact hP.apart 32 8 (by decide) 0xa962 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 32 8 (by decide) 0xa911 122 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10a967 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 86 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa970 (by decide))⟩
    · x86_norm
      exact hP.writable 40 (by decide) (by decide)
    · x86_norm
      exact hP.apart 40 8 (by decide) 0xa967 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 40 8 (by decide) 0xa911 122 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10a970 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 95 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa979 (by decide))⟩
    · x86_norm
      exact hP.writable 48 (by decide) (by decide)
    · x86_norm
      exact hP.apart 48 8 (by decide) 0xa970 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 48 8 (by decide) 0xa911 122 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10a979 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 104 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa982 (by decide))⟩
    · x86_norm
      exact hP.writable 56 (by decide) (by decide)
    · x86_norm
      exact hP.apart 56 8 (by decide) 0xa979 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 56 8 (by decide) 0xa911 122 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10a982 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a911 bytes 113 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, boundary_ne_program outside (inProgram_of_textOffset 0xa98b (by decide))⟩
    · x86_norm
      exact hP.writable 64 (by decide) (by decide)
    · x86_norm
      exact hP.apart 64 8 (by decide) 0xa982 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 64 8 (by decide) 0xa911 122 (by decide)
  apply AdvanceTriple.block_end
  intro s t hp he
  have load (m : Ram) (offset j : Nat) (ho : offset + 8 ≤ 440) (hj : j + 8 ≤ 32) :
      memLoad (memStore m (stackPtr s + BitVec.ofNat 64 offset) (0#64))
        ((Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 j) 64 =
      memLoad m ((Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 j) 64 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (hp.separate offset ho j hj)
  let memory := memStore (memStore (memStore (memStore s.external
    (stackPtr s + 328) (0#64)) (stackPtr s + 320) (0#64))
    (stackPtr s + 312) (0#64)) (stackPtr s + 304) (0#64)
  have preserved (j : Nat) (hj : j + 8 ≤ 32) :
      memLoad memory ((Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 j) 64 =
        memLoad s.external ((Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 j) 64 := by
    dsimp only [memory]
    exact (load _ 304 j (by decide) hj).trans ((load _ 312 j (by decide) hj).trans
      ((load _ 320 j (by decide) hj).trans (load _ 328 j (by decide) hj)))
  have p0 := preserved 0 (by decide)
  have p8 := preserved 8 (by decide)
  have p16 := preserved 16 (by decide)
  have p24 := preserved 24 (by decide)
  simp only [memory, stackPtr, Operand.read_reg64, BitVec.ofNat_eq_ofNat] at p0 p8 p16 p24
  have writeReg (v : RamState) (r : BitVec 5) (x : BitVec 64) :
      ((Operand.reg r : Operand 64).write v x).external = v.external := rfl
  have writeMem (v : RamState) (a x : BitVec 64) :
      ((Operand.mem a : Operand 64).write v x).external = memStore v.external a x := rfl
  have readMem (v : RamState) (a : BitVec 64) :
      (Operand.mem a : Operand 64).read v = memLoad v.external a 64 := rfl
  apply he.weaken
  · rfl
  · x86_norm [effect, stackPtr, writeReg, writeMem]
    simp only [Operand.read_reg64, Int.reduceToNat, Fin.getElem_fin, readMem, gprNumber,
      BitVec.toNat_ofNat, Nat.pow_one, Nat.zero_mod, Nat.zero_shiftLeft, rexR,
      UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', Nat.add_zero, Nat.reducePow, modrmReg,
      Nat.mod_succ, Nat.zero_add, BitVec.add_right_inj, BitVec.reduceEq, false_and, true_and,
      or_self, or_false, false_or, or_true, and_self, and_true]
    exact ⟨p24.symm, p16.symm, p0.symm, p8.symm, p0.symm, p8.symm, p16.symm, p24.symm⟩
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect, stackPtr, writeReg, writeMem]
    simp [Operand.read_reg64]

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a911 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa911 bytes (by decide +kernel) (by decide +kernel)

end P256.Proofs.Nonce.UpdateValue.Prepare.Key.Setup
