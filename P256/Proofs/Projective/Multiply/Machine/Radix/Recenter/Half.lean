import P256.Proofs.Projective.Multiply.Machine.Radix.Store
import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter.AddLoad
import P256.Proofs.Keygen.Multiply.Projective.Radix.Instructions.Shift
import P256.Proofs.Keygen.Multiply.Projective.Lookup.Instructions.Sub
import P256.Proofs.Common.EffectCompose.ByteLogic
import P256.Proofs.Common.Instructions.Lea32
import P256.Proofs.Common.Field.Operations.Run.Compose
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

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step)
open P256.Proofs.Common.Instructions.ByteLogic (and_r8_imm8_effect_step)
open P256.Proofs.Common.Instructions.Lea32 (leaR32Effect lea_r32_legacy_effect_step)

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Recenter

open X86 X86.Machine X86.UserProcess X86Proofs

open P256.Proofs.Keygen.Multiply.ProjectiveRadix.Instructions P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions

attribute [local x86_compose] P256.Proofs.Common.Instructions.sarFlags leaR32Effect
  BitVec.shiftLeft_zero BitVec.setWidth_setWidth_of_le BitVec.setWidth_setWidth

@[x86_compose] theorem memLoad_memStore_indexed (mem : Ram) (base index a b : BitVec 64)
    (v : BitVec 8) (apart : OffsetsApart a 1 b 1) :
    memLoad (memStore mem (base + (index+a)) v) (base + (index+b)) 8 =
      memLoad mem (base + (index+b)) 8 := by
  simpa only [BitVec.add_assoc] using
    memLoad_memStore_apart mem (base+index) a b v 8 apart (by decide) (by decide)

def halfAddress (s : RamState) (offset : BitVec 64) : BitVec 64 :=
  (Operand.reg 4 : Operand 64).read s + ((Operand.reg 1 : Operand 64).read s + offset)

structure HalfPre (p : BitVec 64) (offset : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  readable : MemReadable s (halfAddress s (offset+1)) 1
  writable : MemWritable s (halfAddress s offset) 1
  apart : ∀ start len : Nat, start + len ≤ 23 →
    RangeApart (halfAddress s offset) 1 (p + BitVec.ofNat 64 start) len

def halfEffect (p : BitVec 64) (src dst : BitVec 5) (offset : BitVec 64) (s : RamState) : Effect :=
  let a := (Operand.reg src : Operand 64).read s
  let b := ((a + 8).setWidth 32).setWidth 64
  let mask := mergeGPR 8 (b.setWidth 8 &&& 240) b
  let center := mergeGPR 8 (a.setWidth 8 - mask.setWidth 8) a
  let c := mergeGPR 8 ((b.setWidth 8).sshiftRight 4) b
  let next := mergeGPR 8 (c.setWidth 8 +
    (Operand.mem (halfAddress s (offset+1)) : Operand 8).read s) c
  { rip := p + 23
    writes := [⟨(Operand.reg src : Operand 64), center⟩,
      ⟨(Operand.reg dst : Operand 64), next⟩,
      ⟨(Operand.reg 6 : Operand 64), mask⟩,
      ⟨(Operand.mem (halfAddress s offset) : Operand 8), center.setWidth 8⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

def firstHalfBytes : List UInt8 := [141, 80, 8, 137, 214, 64, 128, 230, 240, 64, 40, 240, 136, 68, 12, 6, 192, 250, 4, 2, 84, 12, 7]

theorem first_half_block [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (next : ∀ offset ∈ ([3,5,9,12,16,19,23] : List Nat), p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (HalfPre p 6) (codeRange p firstHalfBytes)
      (Effect.post (halfEffect p 0 2 6)) := by
  advance_begin (lea_r32_legacy_effect_step p 2 (.base 0 (.d8 8)) (by decide) rfl rfl)
  case next => exact fun s h => next 3 (by simp)
  advance_then (mov_r32_r32_effect_step (p+3) 214 rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 5 (by simp)
  advance_then (and_r8_imm8_effect_step (p+5) 0x40 0xe6 240 (by simp [RexPrefix]) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 9 (by simp)
  advance_then (sub_r8_r8_rex_effect_step (p+9) 0x40 240 (by simp [RexPrefix]) rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 12 (by simp)
  advance_then (mov_m8_r8_legacy_effect_step (p+12) 0 (by decide)
    (.sib 4 (some 1) 0 (.d8 6)) (by decide) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      exact hP.apart 12 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (halfAddress s 6) 1 p 23
      intro i hi j hj he
      exact hP.apart 0 23 (by decide) i hi j hj (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he)
    · x86_norm
      exact next 16 (by simp)
  advance_then (sar_byte_four_effect_step (p+16) 250 rfl rfl (by decide))
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 19 (by simp)
  advance_then (add_r8_m8_effect_step (p+19) 2 (by decide)
    (.sib 4 (some 1) 0 (.d8 7)) (by decide) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable
    · x86_avoid
    · x86_norm
      exact next 23 (by simp)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [halfEffect,halfAddress,addSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [halfEffect,halfAddress,addSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [halfEffect,halfAddress,addSpec]
  · x86_norm [halfEffect,halfAddress,addSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def secondHalfBytes : List UInt8 := [141, 66, 8, 137, 198, 64, 128, 230, 240, 64, 40, 242, 136, 84, 12, 7, 192, 248, 4, 2, 68, 12, 8]

theorem second_half_block [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (next : ∀ offset ∈ ([3,5,9,12,16,19,23] : List Nat), p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (HalfPre p 7) (codeRange p secondHalfBytes)
      (Effect.post (halfEffect p 2 0 7)) := by
  advance_begin (lea_r32_legacy_effect_step p 0 (.base 2 (.d8 8)) (by decide) rfl rfl)
  case next => exact fun s h => next 3 (by simp)
  advance_then (mov_r32_r32_effect_step (p+3) 198 rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 5 (by simp)
  advance_then (and_r8_imm8_effect_step (p+5) 0x40 0xe6 240 (by simp [RexPrefix]) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 9 (by simp)
  advance_then (sub_r8_r8_rex_effect_step (p+9) 0x40 242 (by simp [RexPrefix]) rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 12 (by simp)
  advance_then (mov_m8_r8_legacy_effect_step (p+12) 2 (by decide)
    (.sib 4 (some 1) 0 (.d8 7)) (by decide) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      exact hP.apart 12 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (halfAddress s 7) 1 p 23
      intro i hi j hj he
      exact hP.apart 0 23 (by decide) i hi j hj (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he)
    · x86_norm
      exact next 16 (by simp)
  advance_then (sar_byte_four_effect_step (p+16) 248 rfl rfl (by decide))
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 19 (by simp)
  advance_then (add_r8_m8_effect_step (p+19) 0 (by decide)
    (.sib 4 (some 1) 0 (.d8 8)) (by decide) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable
    · x86_avoid
    · x86_norm
      exact next 23 (by simp)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [halfEffect,halfAddress,addSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [halfEffect,halfAddress,addSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [halfEffect,halfAddress,addSpec]
  · x86_norm [halfEffect,halfAddress,addSpec]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Radix.Recenter
