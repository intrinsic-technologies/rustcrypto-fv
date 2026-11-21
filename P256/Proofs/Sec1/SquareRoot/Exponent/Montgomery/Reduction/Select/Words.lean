import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Common
import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Common.Instructions.Neg64
import P256.Proofs.Common.EffectCompose.Memory
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
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mov_m8_r8_effect_step)
open P256.Proofs.Common.Instructions.Neg64 (negR64Effect neg_r64_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

@[x86_local] theorem mask_neg_local (p : BitVec 64) (r : BitVec 5) :
    Effect.Local (negR64Effect p r) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [negR64Effect, h.read_reg]
  · intro s
    simp [negR64Effect, Write.Full, Operand.Full]

attribute [x86_compose] negR64Effect

structure MaskWordPre (p : BitVec 64) (len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : MemWritable s (stackPtr s+8) 1
  apart : RangeApart (stackPtr s+8) 1 p len

def maskWordEffect (p : BitVec 64) (len : Nat) (dst orig diff : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg orig : Operand 64).read s
  let r := (Operand.reg diff : Operand 64).read s
  let q := (Operand.reg 5 : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), selectWord a r (q.setWidth 64)⟩,
      ⟨(Operand.reg orig : Operand 64), a ^^^ r⟩,
      ⟨(Operand.mem (stackPtr s+8) : Operand 8), q⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def maskLowBytes : List UInt8 :=
  [0x40, 0x88, 0x6c, 0x24, 0x8, 0x44, 0xf, 0xb6, 0x54, 0x24, 0x8, 0x4c, 0x31, 0xc1, 0x49, 0xf7, 0xda, 0x49, 0x21, 0xca, 0x4d, 0x31, 0xc2]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem mask_low_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 23 →
      p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (MaskWordPre p 23) (codeRange p maskLowBytes)
      (Effect.post (maskWordEffect p 23 10 1 8)) := by
  advance_begin (show StepEffect _ _ (storeEffect p 5 (fun s => stackPtr s+8)
      (fun s => (Operand.reg 5 : Operand 8).read s)) from
    mov_m8_r8_effect_step p 0x40 (by simp [RexPrefix]) 5
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, h.writable, ?_⟩
    intro i hi j hj
    change j < 5 at hj
    exact h.apart i hi j (by omega)
  case next =>
    intro s h
    x86_norm [BitVec.add_assoc]
    exact next 5 (by decide) (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart
  advance_then (show StepEffect _ _ (movzxR32M8Effect (p+5#64) 6 10 (.sib 4 none 0 (.d8 8))) from
    movzx_r_m8_rex_effect_step (p+5#64) 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (fun _ => rfl) 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p maskLowBytes 5 6)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 11 (by decide) (by decide)
  advance_then (show StepEffect _ _ (xorR64R64Effect (p+11#64) 1 8) from
    xor_r64_r64_effect_step (p+11#64) 0x4c 0xc1 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskLowBytes 11 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 14 (by decide) (by decide)
  advance_then (show StepEffect _ _ (negR64Effect (p+14#64) 10) from
    neg_r64_effect_step (p+14#64) 0x49 0xda (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset p maskLowBytes 14 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, negR64Effect, Effect.components]
    · x86_norm [BitVec.add_assoc]
      exact next 17 (by decide) (by decide)
  advance_then (show StepEffect _ _ (andR64R64Effect (p+17#64) 10 1) from
    and_r64_r64_effect_step (p+17#64) 0x49 0xca (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskLowBytes 17 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 20 (by decide) (by decide)
  advance_then (show StepEffect _ _ (xorR64R64Effect (p+20#64) 10 8) from
    xor_r64_r64_effect_step (p+20#64) 0x4d 0xc2 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskLowBytes 20 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 23 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]
  · intro i; cases i <;> exact .inl rfl
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]

def maskMiddleLowBytes : List UInt8 :=
  [0x40, 0x88, 0x6c, 0x24, 0x8, 0xf, 0xb6, 0x4c, 0x24, 0x8, 0x4c, 0x31, 0xce, 0x48, 0xf7, 0xd9, 0x48, 0x21, 0xf1, 0x4c, 0x31, 0xc9]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem mask_middleLow_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 22 →
      p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (MaskWordPre p 22) (codeRange p maskMiddleLowBytes)
      (Effect.post (maskWordEffect p 22 1 6 9)) := by
  advance_begin (show StepEffect _ _ (storeEffect p 5 (fun s => stackPtr s+8)
      (fun s => (Operand.reg 5 : Operand 8).read s)) from
    mov_m8_r8_effect_step p 0x40 (by simp [RexPrefix]) 5
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, h.writable, ?_⟩
    intro i hi j hj
    change j < 5 at hj
    exact h.apart i hi j (by omega)
  case next =>
    intro s h
    x86_norm [BitVec.add_assoc]
    exact next 5 (by decide) (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart
  advance_then (show StepEffect _ _ (movzxR32M8Effect (p+5#64) 5 1 (.sib 4 none 0 (.d8 8))) from
    movzx_r32_m8_effect_step (p+5#64) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p maskMiddleLowBytes 5 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 10 (by decide) (by decide)
  advance_then (show StepEffect _ _ (xorR64R64Effect (p+10#64) 6 9) from
    xor_r64_r64_effect_step (p+10#64) 0x4c 0xce (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskMiddleLowBytes 10 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 13 (by decide) (by decide)
  advance_then (show StepEffect _ _ (negR64Effect (p+13#64) 1) from
    neg_r64_effect_step (p+13#64) 0x48 0xd9 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset p maskMiddleLowBytes 13 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, negR64Effect, Effect.components]
    · x86_norm [BitVec.add_assoc]
      exact next 16 (by decide) (by decide)
  advance_then (show StepEffect _ _ (andR64R64Effect (p+16#64) 1 6) from
    and_r64_r64_effect_step (p+16#64) 0x48 0xf1 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskMiddleLowBytes 16 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 19 (by decide) (by decide)
  advance_then (show StepEffect _ _ (xorR64R64Effect (p+19#64) 1 9) from
    xor_r64_r64_effect_step (p+19#64) 0x4c 0xc9 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskMiddleLowBytes 19 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 22 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]
  · intro i; cases i <;> exact .inl rfl
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]

def maskMiddleHighBytes : List UInt8 :=
  [0x40, 0x88, 0x6c, 0x24, 0x8, 0xf, 0xb6, 0x74, 0x24, 0x8, 0x4c, 0x31, 0xd8, 0x48, 0xf7, 0xde, 0x48, 0x21, 0xc6, 0x4c, 0x31, 0xde]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem mask_middleHigh_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 22 →
      p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (MaskWordPre p 22) (codeRange p maskMiddleHighBytes)
      (Effect.post (maskWordEffect p 22 6 0 11)) := by
  advance_begin (show StepEffect _ _ (storeEffect p 5 (fun s => stackPtr s+8)
      (fun s => (Operand.reg 5 : Operand 8).read s)) from
    mov_m8_r8_effect_step p 0x40 (by simp [RexPrefix]) 5
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, h.writable, ?_⟩
    intro i hi j hj
    change j < 5 at hj
    exact h.apart i hi j (by omega)
  case next =>
    intro s h
    x86_norm [BitVec.add_assoc]
    exact next 5 (by decide) (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart
  advance_then (show StepEffect _ _ (movzxR32M8Effect (p+5#64) 5 6 (.sib 4 none 0 (.d8 8))) from
    movzx_r32_m8_effect_step (p+5#64) 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p maskMiddleHighBytes 5 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 10 (by decide) (by decide)
  advance_then (show StepEffect _ _ (xorR64R64Effect (p+10#64) 0 11) from
    xor_r64_r64_effect_step (p+10#64) 0x4c 0xd8 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskMiddleHighBytes 10 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 13 (by decide) (by decide)
  advance_then (show StepEffect _ _ (negR64Effect (p+13#64) 6) from
    neg_r64_effect_step (p+13#64) 0x48 0xde (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset p maskMiddleHighBytes 13 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, negR64Effect, Effect.components]
    · x86_norm [BitVec.add_assoc]
      exact next 16 (by decide) (by decide)
  advance_then (show StepEffect _ _ (andR64R64Effect (p+16#64) 6 0) from
    and_r64_r64_effect_step (p+16#64) 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskMiddleHighBytes 16 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 19 (by decide) (by decide)
  advance_then (show StepEffect _ _ (xorR64R64Effect (p+19#64) 6 11) from
    xor_r64_r64_effect_step (p+19#64) 0x4c 0xde (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskMiddleHighBytes 19 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 22 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]
  · intro i; cases i <;> exact .inl rfl
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]

def maskHighBytes : List UInt8 :=
  [0x40, 0x88, 0x6c, 0x24, 0x8, 0xf, 0xb6, 0x44, 0x24, 0x8, 0x4c, 0x31, 0xf2, 0x48, 0xf7, 0xd8, 0x48, 0x21, 0xd0, 0x4c, 0x31, 0xf0]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem mask_high_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 22 →
      p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (MaskWordPre p 22) (codeRange p maskHighBytes)
      (Effect.post (maskWordEffect p 22 0 2 14)) := by
  advance_begin (show StepEffect _ _ (storeEffect p 5 (fun s => stackPtr s+8)
      (fun s => (Operand.reg 5 : Operand 8).read s)) from
    mov_m8_r8_effect_step p 0x40 (by simp [RexPrefix]) 5
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, h.writable, ?_⟩
    intro i hi j hj
    change j < 5 at hj
    exact h.apart i hi j (by omega)
  case next =>
    intro s h
    x86_norm [BitVec.add_assoc]
    exact next 5 (by decide) (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart
  advance_then (show StepEffect _ _ (movzxR32M8Effect (p+5#64) 5 0 (.sib 4 none 0 (.d8 8))) from
    movzx_r32_m8_effect_step (p+5#64) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p maskHighBytes 5 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 10 (by decide) (by decide)
  advance_then (show StepEffect _ _ (xorR64R64Effect (p+10#64) 2 14) from
    xor_r64_r64_effect_step (p+10#64) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskHighBytes 10 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 13 (by decide) (by decide)
  advance_then (show StepEffect _ _ (negR64Effect (p+13#64) 0) from
    neg_r64_effect_step (p+13#64) 0x48 0xd8 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset p maskHighBytes 13 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, negR64Effect, Effect.components]
    · x86_norm [BitVec.add_assoc]
      exact next 16 (by decide) (by decide)
  advance_then (show StepEffect _ _ (andR64R64Effect (p+16#64) 0 2) from
    and_r64_r64_effect_step (p+16#64) 0x48 0xd0 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskHighBytes 16 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 19 (by decide) (by decide)
  advance_then (show StepEffect _ _ (xorR64R64Effect (p+19#64) 0 14) from
    xor_r64_r64_effect_step (p+19#64) 0x4c 0xf0 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p maskHighBytes 19 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 22 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]
  · intro i; cases i <;> exact .inl rfl
  · x86_norm [maskWordEffect, selectWord, stackPtr, Operand.read_reg64]

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
