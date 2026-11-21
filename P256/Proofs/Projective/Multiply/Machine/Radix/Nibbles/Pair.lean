import P256.Proofs.Keygen.Multiply.Projective.Radix.Instructions.Shift
import P256.Proofs.Projective.Multiply.Machine.Radix.Store
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.EffectCompose.ByteLogic
import P256.Proofs.Common.Instructions.ByteLogic.And
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
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
import X86Proofs.Program.Entry

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step)
open P256.Proofs.Common.Instructions.ByteLogic (andR8Imm8Effect and_r8_imm8_legacy_effect_step)

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open X86 X86.Machine X86.UserProcess X86Proofs

open P256.Proofs.Keygen.Multiply.ProjectiveRadix.Instructions

structure PairPre (p : BitVec 64) (src lo hi : BitVec 8) (s : RamState) : Prop where
  rip : s.RIP = p
  readable : MemReadable s ((Operand.reg 4 : Operand 64).read s + src.signExtend 64) 1
  writable : ∀ offset ∈ [lo,hi],
    MemWritable s ((Operand.reg 4 : Operand 64).read s + offset.signExtend 64) 1
  apart : OffsetsApart (hi.signExtend 64) 1 (lo.signExtend 64) 1
  codeApart : ∀ offset ∈ [lo,hi], ∀ start len : Nat, start + len ≤ 21 →
    RangeApart ((Operand.reg 4 : Operand 64).read s + offset.signExtend 64) 1
      (p + BitVec.ofNat 64 start) len

def pairBytes (src lo hi : BitVec 8) : List UInt8 :=
  [0x0f,0xb6,0x4c,0x24,UInt8.ofBitVec src,0x89,0xca,0x80,0xe2,0x0f,
   0x88,0x54,0x24,UInt8.ofBitVec lo,0xc0,0xe9,4,0x88,0x4c,0x24,UInt8.ofBitVec hi]

def pairEffect (p : BitVec 64) (src lo hi : BitVec 8) (s : RamState) : Effect :=
  let b := (Operand.mem ((Operand.reg 4 : Operand 64).read s + src.signExtend 64) : Operand 8).read s
  { rip := p + 21
    writes := [
      ⟨(Operand.reg 1 : Operand 64), mergeGPR 8 (b >>> 4) (b.setWidth 64)⟩,
      ⟨(Operand.reg 2 : Operand 64), mergeGPR 8 (b &&& 15) (b.setWidth 64)⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + lo.signExtend 64) : Operand 8), b &&& 15⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + hi.signExtend 64) : Operand 8), b >>> 4⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

attribute [local x86_compose] BitVec.setWidth_setWidth_of_le BitVec.setWidth_setWidth

theorem pair_block [Bindings] (boundary : ReturnBoundary) (p : BitVec 64) (src lo hi : BitVec 8)
    (next : ∀ offset ∈ ([5,7,10,14,17,21] : List Nat), p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (PairPre p src lo hi) (codeRange p (pairBytes src lo hi))
      (Effect.post (pairEffect p src lo hi)) := by
  advance_begin (movzx_r32_m8_effect_step p 1 (.sib 4 none 0 (.d8 src)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [pairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (pairBytes src lo hi) 0 5
  case pre =>
    intro s h
    exact ⟨h.rip,h.readable⟩
  case next => exact fun s h => next 5 (by simp)
  advance_then (mov_r32_r32_effect_step (p+5) 0xca rfl)
  case sub =>
    simpa [pairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (pairBytes src lo hi) 5 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 7 (by simp)
  advance_then (and_r8_imm8_legacy_effect_step (p+7) 0xe2 15 rfl rfl (by decide))
  case sub =>
    simpa [pairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (pairBytes src lo hi) 7 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [andR8Imm8Effect, Effect.components, Component.Covers]
    · x86_norm
      exact next 10 (by simp)
  advance_then (mov_m8_r8_legacy_effect_step (p+10) 2 (by decide)
    (.sib 4 none 0 (.d8 lo)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [pairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (pairBytes src lo hi) 10 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable lo (by simp)
    · x86_norm
      exact hP.codeApart lo (by simp) 10 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa [pairBytes] using hP.codeApart lo (by simp) 0 21 (by decide)
    · x86_norm
      exact next 14 (by simp)
  advance_then (shr_byte_four_effect_step (p+14) 0xe9 rfl rfl (by decide))
  case sub =>
    simpa [pairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (pairBytes src lo hi) 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [shrByteFourEffect, Effect.components, Component.Covers]
    · x86_norm
      exact next 17 (by simp)
  advance_then (mov_m8_r8_legacy_effect_step (p+17) 1 (by decide)
    (.sib 4 none 0 (.d8 hi)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [pairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (pairBytes src lo hi) 17 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable hi (by simp)
    · x86_norm
      exact hP.codeApart hi (by simp) 17 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa [pairBytes] using hP.codeApart hi (by simp) 0 21 (by decide)
    · x86_norm
      exact next 21 (by simp)
  apply AdvanceTriple.block_end
  intro s t hP hH
  have apart := hP.apart
  have memApart (m : Ram) (b : BitVec 64) (v : BitVec 8) :=
    memLoad_memStore_apart m b (hi.signExtend 64) (lo.signExtend 64) v 8 apart (by decide) (by decide)
  apply hH.weaken
  · x86_norm [pairEffect,memApart,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
    all_goals first | solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl] | skip
  · x86_norm [pairEffect,memApart,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
    all_goals first | solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl] | skip
  · intro i; cases i <;> x86_norm [pairEffect,memApart,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
  · x86_norm [pairEffect,memApart,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
    all_goals first | solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl] | skip

end P256.Proofs.Projective.Multiply.Machine.Radix
