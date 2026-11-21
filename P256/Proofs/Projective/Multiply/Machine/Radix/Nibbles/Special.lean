import P256.Proofs.Common.Instructions.ByteOps.Effects
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
open P256.Proofs.Common.Instructions (mov_m8_r8_effect_step mov_m8_r8_legacy_effect_step)
open P256.Proofs.Common.Instructions.ByteLogic (andR8Imm8Effect and_r8_imm8_effect_step and_r8_imm8_legacy_effect_step)

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open X86 X86.Machine X86.UserProcess X86Proofs

open P256.Proofs.Keygen.Multiply.ProjectiveRadix.Instructions

structure FirstPairPre (p : BitVec 64) (src lo hi : BitVec 8) (s : RamState) : Prop where
  rip : s.RIP = p
  readable : MemReadable s ((Operand.reg 4 : Operand 64).read s + src.signExtend 64) 1
  writable : ∀ offset ∈ [lo,hi],
    MemWritable s ((Operand.reg 4 : Operand 64).read s + offset.signExtend 64) 1
  apart : OffsetsApart (hi.signExtend 64) 1 (lo.signExtend 64) 1
  codeApart : ∀ offset ∈ [lo,hi], ∀ start len : Nat, start + len ≤ 20 →
    RangeApart ((Operand.reg 4 : Operand 64).read s + offset.signExtend 64) 1
      (p + BitVec.ofNat 64 start) len

def firstPairBytes (src lo hi : BitVec 8) : List UInt8 :=
  [0x0f,0xb6,0x4c,0x24,UInt8.ofBitVec src,0x89,0xc8,0x24,0x0f,
   0x88,0x44,0x24,UInt8.ofBitVec lo,0xc0,0xe9,4,0x88,0x4c,0x24,UInt8.ofBitVec hi]

def firstPairEffect (p : BitVec 64) (src lo hi : BitVec 8) (s : RamState) : Effect :=
  let b := (Operand.mem ((Operand.reg 4 : Operand 64).read s + src.signExtend 64) : Operand 8).read s
  { rip := p + 20
    writes := [
      ⟨(Operand.reg 1 : Operand 64), mergeGPR 8 (b >>> 4) (b.setWidth 64)⟩,
      ⟨(Operand.reg 0 : Operand 64), mergeGPR 8 (b &&& 15) (b.setWidth 64)⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + lo.signExtend 64) : Operand 8), b &&& 15⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + hi.signExtend 64) : Operand 8), b >>> 4⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

attribute [local x86_compose] BitVec.setWidth_setWidth_of_le BitVec.setWidth_setWidth

set_option maxHeartbeats 800000 in
theorem firstPair_block [Bindings] (boundary : ReturnBoundary) (p : BitVec 64) (src lo hi : BitVec 8)
    (next : ∀ offset ∈ ([5,7,9,13,16,20] : List Nat), p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (FirstPairPre p src lo hi) (codeRange p (firstPairBytes src lo hi))
      (Effect.post (firstPairEffect p src lo hi)) := by
  advance_begin (movzx_r32_m8_effect_step p 1 (.sib 4 none 0 (.d8 src)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [firstPairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (firstPairBytes src lo hi) 0 5
  case pre =>
    intro s h
    exact ⟨h.rip,h.readable⟩
  case next => exact fun s h => next 5 (by simp)
  advance_then (mov_r32_r32_effect_step (p+5) 0xc8 rfl)
  case sub =>
    simpa [firstPairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (firstPairBytes src lo hi) 5 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 7 (by simp)
  advance_then (show StepEffect (fun (s : RamState) => s.RIP = p+(7 : BitVec 64))
    (codeRange (p+7) [0x24,15]) (andR8Imm8Effect (p+7) 2 0 15) from
      P256.Proofs.Common.Instructions.ByteOps.ByteOps.and_al_imm8_effect_step (p+7) 15)
  case sub =>
    simpa [firstPairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (firstPairBytes src lo hi) 7 2
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [andR8Imm8Effect, Effect.components, Component.Covers]
    · x86_norm
      exact next 9 (by simp)
  advance_then (mov_m8_r8_legacy_effect_step (p+9) 0 (by decide)
    (.sib 4 none 0 (.d8 lo)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [firstPairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (firstPairBytes src lo hi) 9 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable lo (by simp)
    · x86_norm
      exact hP.codeApart lo (by simp) 9 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa [firstPairBytes] using hP.codeApart lo (by simp) 0 20 (by decide)
    · x86_norm
      exact next 13 (by simp)
  advance_then (shr_byte_four_effect_step (p+13) 0xe9 rfl rfl (by decide))
  case sub =>
    simpa [firstPairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (firstPairBytes src lo hi) 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [shrByteFourEffect, Effect.components, Component.Covers]
    · x86_norm
      exact next 16 (by simp)
  advance_then (mov_m8_r8_legacy_effect_step (p+16) 1 (by decide)
    (.sib 4 none 0 (.d8 hi)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [firstPairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (firstPairBytes src lo hi) 16 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable hi (by simp)
    · x86_norm
      exact hP.codeApart hi (by simp) 16 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa [firstPairBytes] using hP.codeApart hi (by simp) 0 20 (by decide)
    · x86_norm
      exact next 20 (by simp)
  apply AdvanceTriple.block_end
  intro s t hP hH
  have apart := hP.apart
  have memApart (m : Ram) (b : BitVec 64) (v : BitVec 8) :=
    memLoad_memStore_apart m b (hi.signExtend 64) (lo.signExtend 64) v 8 apart (by decide) (by decide)
  apply hH.weaken
  · x86_norm [firstPairEffect,memApart,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
    all_goals first | solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl] | skip
  · x86_norm [firstPairEffect,memApart,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
    all_goals first | solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl] | skip
  · intro i; cases i <;> x86_norm [firstPairEffect,memApart,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
  · x86_norm [firstPairEffect,memApart,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
    all_goals first | solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl] | skip

structure DoublePairPre (p : BitVec 64) (srcFirst srcNext loFirst hiFirst loNext hiNext : BitVec 8)
    (s : RamState) : Prop where
  rip : s.RIP = p
  readable : ∀ offset ∈ [srcFirst,srcNext],
    MemReadable s ((Operand.reg 4 : Operand 64).read s + offset.signExtend 64) 1
  writable : ∀ offset ∈ [loFirst,hiFirst,loNext,hiNext],
    MemWritable s ((Operand.reg 4 : Operand 64).read s + offset.signExtend 64) 1
  apart :
    OffsetsApart (hiFirst.signExtend 64) 1 (loFirst.signExtend 64) 1 ∧
    OffsetsApart (loNext.signExtend 64) 1 (loFirst.signExtend 64) 1 ∧
    OffsetsApart (loNext.signExtend 64) 1 (hiFirst.signExtend 64) 1 ∧
    OffsetsApart (hiNext.signExtend 64) 1 (loFirst.signExtend 64) 1 ∧
    OffsetsApart (hiNext.signExtend 64) 1 (hiFirst.signExtend 64) 1 ∧
    OffsetsApart (hiNext.signExtend 64) 1 (loNext.signExtend 64) 1
  codeApart : ∀ offset ∈ [loFirst,hiFirst,loNext,hiNext], ∀ start len : Nat, start + len ≤ 44 →
    RangeApart ((Operand.reg 4 : Operand 64).read s + offset.signExtend 64) 1
      (p + BitVec.ofNat 64 start) len

def doublePairBytes (srcFirst srcNext loFirst hiFirst loNext hiNext : BitVec 8) : List UInt8 :=
  [0x0f,0xb6,0x4c,0x24,UInt8.ofBitVec srcNext,
   0x0f,0xb6,0x54,0x24,UInt8.ofBitVec srcFirst,
   0x89,0xd6,0x40,0x80,0xe6,0x0f,0x40,0x88,0x74,0x24,UInt8.ofBitVec loFirst,
   0xc0,0xea,4,0x88,0x54,0x24,UInt8.ofBitVec hiFirst,
   0x89,0xca,0x80,0xe2,0x0f,0x88,0x54,0x24,UInt8.ofBitVec loNext,
   0xc0,0xe9,4,0x88,0x4c,0x24,UInt8.ofBitVec hiNext]

def doublePairEffect (p : BitVec 64) (srcFirst srcNext loFirst hiFirst loNext hiNext : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.mem ((Operand.reg 4 : Operand 64).read s + srcFirst.signExtend 64) : Operand 8).read s
  let b := (Operand.mem ((Operand.reg 4 : Operand 64).read s + srcNext.signExtend 64) : Operand 8).read s
  { rip := p + 44
    writes := [
      ⟨(Operand.reg 1 : Operand 64), mergeGPR 8 (b >>> 4) (b.setWidth 64)⟩,
      ⟨(Operand.reg 2 : Operand 64), mergeGPR 8 (b &&& 15) (b.setWidth 64)⟩,
      ⟨(Operand.reg 6 : Operand 64), mergeGPR 8 (a &&& 15) (a.setWidth 64)⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + loFirst.signExtend 64) : Operand 8), a &&& 15⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + hiFirst.signExtend 64) : Operand 8), a >>> 4⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + loNext.signExtend 64) : Operand 8), b &&& 15⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + hiNext.signExtend 64) : Operand 8), b >>> 4⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

set_option maxHeartbeats 1600000 in
theorem doublePair_block [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (srcFirst srcNext loFirst hiFirst loNext hiNext : BitVec 8)
    (next : ∀ offset ∈ ([5,10,12,16,21,24,28,30,33,37,40,44] : List Nat),
      p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (DoublePairPre p srcFirst srcNext loFirst hiFirst loNext hiNext)
      (codeRange p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext))
      (Effect.post (doublePairEffect p srcFirst srcNext loFirst hiFirst loNext hiNext)) := by
  advance_begin (movzx_r32_m8_effect_step p 1 (.sib 4 none 0 (.d8 srcNext)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 0 5
  case pre =>
    intro s h
    exact ⟨h.rip,h.readable srcNext (by simp)⟩
  case next => exact fun s h => next 5 (by simp)
  advance_then (movzx_r32_m8_effect_step (p+5) 2 (.sib 4 none 0 (.d8 srcFirst)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable srcFirst (by simp)
    · x86_avoid
    · x86_norm
      exact next 10 (by simp)
  advance_then (mov_r32_r32_effect_step (p+10) 0xd6 rfl)
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 10 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 12 (by simp)
  advance_then (and_r8_imm8_effect_step (p+12) 0x40 0xe6 15 (by simp [RexPrefix]) rfl rfl)
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 12 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 16 (by simp)
  advance_then (mov_m8_r8_effect_step (p+16) 0x40 (by simp [RexPrefix]) 6 (.sib 4 none 0 (.d8 loFirst)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 16 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable loFirst (by simp)
    · x86_norm
      exact hP.codeApart loFirst (by simp) 16 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa [doublePairBytes] using hP.codeApart loFirst (by simp) 0 44 (by decide)
    · x86_norm
      exact next 21 (by simp)
  advance_then (shr_byte_four_effect_step (p+21) 0xea rfl rfl (by decide))
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 21 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 24 (by simp)
  advance_then (mov_m8_r8_legacy_effect_step (p+24) 2 (by decide) (.sib 4 none 0 (.d8 hiFirst)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 24 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable hiFirst (by simp)
    · x86_norm
      exact hP.codeApart hiFirst (by simp) 24 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa [doublePairBytes] using hP.codeApart hiFirst (by simp) 0 44 (by decide)
    · x86_norm
      exact next 28 (by simp)
  advance_then (mov_r32_r32_effect_step (p+28) 0xca rfl)
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 28 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 30 (by simp)
  advance_then (and_r8_imm8_legacy_effect_step (p+30) 0xe2 15 rfl rfl (by decide))
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 30 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 33 (by simp)
  advance_then (mov_m8_r8_legacy_effect_step (p+33) 2 (by decide) (.sib 4 none 0 (.d8 loNext)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 33 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable loNext (by simp)
    · x86_norm
      exact hP.codeApart loNext (by simp) 33 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa [doublePairBytes] using hP.codeApart loNext (by simp) 0 44 (by decide)
    · x86_norm
      exact next 37 (by simp)
  advance_then (shr_byte_four_effect_step (p+37) 0xe9 rfl rfl (by decide))
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 37 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · x86_norm
      exact next 40 (by simp)
  advance_then (mov_m8_r8_legacy_effect_step (p+40) 1 (by decide) (.sib 4 none 0 (.d8 hiNext)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simpa [doublePairBytes,AddrMode.tail,Disp.bytes,immBytes_eight,AddrMode.modrm,AddrMode.mod,Disp.mod,AddrMode.rm,AddrMode.sibByte,idxLow,regLow] using
      codeRange_slice_subset p (doublePairBytes srcFirst srcNext loFirst hiFirst loNext hiNext) 40 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable hiNext (by simp)
    · x86_norm
      exact hP.codeApart hiNext (by simp) 40 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa [doublePairBytes] using hP.codeApart hiNext (by simp) 0 44 (by decide)
    · x86_norm
      exact next 44 (by simp)
  apply AdvanceTriple.block_end
  intro s t hP hH
  obtain ⟨apart10,apart20,apart21,apart30,apart31,apart32⟩ := hP.apart
  have memApart10 (m : Ram) (b : BitVec 64) (v : BitVec 8) :=
    memLoad_memStore_apart m b (hiFirst.signExtend 64) (loFirst.signExtend 64) v 8 apart10 (by decide) (by decide)
  have memApart20 (m : Ram) (b : BitVec 64) (v : BitVec 8) :=
    memLoad_memStore_apart m b (loNext.signExtend 64) (loFirst.signExtend 64) v 8 apart20 (by decide) (by decide)
  have memApart21 (m : Ram) (b : BitVec 64) (v : BitVec 8) :=
    memLoad_memStore_apart m b (loNext.signExtend 64) (hiFirst.signExtend 64) v 8 apart21 (by decide) (by decide)
  have memApart30 (m : Ram) (b : BitVec 64) (v : BitVec 8) :=
    memLoad_memStore_apart m b (hiNext.signExtend 64) (loFirst.signExtend 64) v 8 apart30 (by decide) (by decide)
  have memApart31 (m : Ram) (b : BitVec 64) (v : BitVec 8) :=
    memLoad_memStore_apart m b (hiNext.signExtend 64) (hiFirst.signExtend 64) v 8 apart31 (by decide) (by decide)
  have memApart32 (m : Ram) (b : BitVec 64) (v : BitVec 8) :=
    memLoad_memStore_apart m b (hiNext.signExtend 64) (loNext.signExtend 64) v 8 apart32 (by decide) (by decide)
  apply hH.weaken
  · x86_norm [doublePairEffect,memApart10,memApart20,memApart21,memApart30,memApart31,memApart32,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
    all_goals first | solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl] | skip
  · x86_norm [doublePairEffect,memApart10,memApart20,memApart21,memApart30,memApart31,memApart32,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
    all_goals first | solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl] | skip
  · intro i; cases i <;> x86_norm [doublePairEffect,memApart10,memApart20,memApart21,memApart30,memApart31,memApart32,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
  · x86_norm [doublePairEffect,memApart10,memApart20,memApart21,memApart30,memApart31,memApart32,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8]
    all_goals first | solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl] | skip

end P256.Proofs.Projective.Multiply.Machine.Radix
