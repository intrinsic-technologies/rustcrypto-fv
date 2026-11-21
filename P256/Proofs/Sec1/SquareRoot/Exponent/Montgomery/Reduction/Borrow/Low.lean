import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Common
import P256.Proofs.Field.Montgomery.Reduction.Slot
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
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

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def borrowLowBytes : List UInt8 :=
  [0x49, 0x89, 0xc8, 0x4c, 0x8b, 0x74, 0x24, 0x20, 0x4d, 0x29, 0xf0, 0x49, 0x89, 0xc9, 0x49, 0xf7, 0xd1, 0x4d, 0x89, 0xf3, 0x4d, 0x21, 0xcb, 0x4d, 0x9, 0xf1, 0x4d, 0x21, 0xc1, 0x4d, 0x9, 0xd9, 0x49, 0xc1, 0xe9, 0x3f, 0x4c, 0x89, 0x4c, 0x24, 0x8, 0x48, 0x8d, 0x5c, 0x24, 0x8, 0x45, 0x31, 0xc9, 0x4c, 0x2b, 0x4c, 0x24, 0x8]

def borrowLowEffect (p : BitVec 64) (s : RamState) : Effect :=
  let a := (Operand.reg 1#5 : Operand 64).read s
  let m := (Operand.mem (stackPtr s + 32#64) : Operand 64).read s
  let r := a-m
  let b := borrow a m r
  { rip := p+54#64
    writes := [⟨(Operand.reg 8#5 : Operand 64), r⟩,
      ⟨(Operand.reg 14#5 : Operand 64), m⟩,
      ⟨(Operand.reg 9#5 : Operand 64), -b⟩,
      ⟨(Operand.reg 11#5 : Operand 64), m &&& ~~~a⟩,
      ⟨(Operand.reg 3#5 : Operand 64), stackPtr s+8#64⟩,
      ⟨(Operand.mem (stackPtr s+8#64) : Operand 64), b⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem borrow_low_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 54 →
      p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p ∧ MemoryPre s ∧
      RangeApart (stackPtr s+8#64) 8 p 54)
      (codeRange p borrowLowBytes) (Effect.post (borrowLowEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect p 8#5 1#5) from
    mov_r64_r64_effect_step p 0x49 0xc8 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 0 3)
  case next =>
    intro s hP
    exact next 3 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+3#64) 14#5 (.sib 4 none 0 (.d8 32))) from
    mov_r64_m64_effect_step (p+3#64) 0x4c (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 3 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.2.1.scratch 32 8 (by decide) (by decide) (by decide)).readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 8 (by decide) (by decide)
  advance_then (show StepEffect _ _ (subR64R64Effect (p+8#64) 8#5 14#5) from
    sub_r64_r64_effect_step (p+8#64) 0x4d 0xf0 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 8 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 11 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+11#64) 9#5 1#5) from
    mov_r64_r64_effect_step (p+11#64) 0x49 0xc9 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 11 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 14 (by decide) (by decide)
  advance_then (show StepEffect _ _ (notR64Effect (p+14#64) 9#5) from
    not_r64_effect_step (p+14#64) 0x49 0xd1 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 14 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 17 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+17#64) 11#5 14#5) from
    mov_r64_r64_effect_step (p+17#64) 0x4d 0xf3 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 17 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 20 (by decide) (by decide)
  advance_then (show StepEffect _ _ (andR64R64Effect (p+20#64) 11#5 9#5) from
    and_r64_r64_effect_step (p+20#64) 0x4d 0xcb (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 20 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 23 (by decide) (by decide)
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.FieldNeg.Instructions.orR64R64Effect (p+23#64) 9#5 14#5) from
    P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step (p+23#64) 0x4d 0xf1 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 23 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 26 (by decide) (by decide)
  advance_then (show StepEffect _ _ (andR64R64Effect (p+26#64) 9#5 8#5) from
    and_r64_r64_effect_step (p+26#64) 0x4d 0xc1 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 26 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 29 (by decide) (by decide)
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.FieldNeg.Instructions.orR64R64Effect (p+29#64) 9#5 11#5) from
    P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step (p+29#64) 0x4d 0xd9 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 29 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 32 (by decide) (by decide)
  advance_then (show StepEffect _ _ (shrR64Effect (p+32#64) 4 9#5 63) from
    shr_r64_imm8_effect_step (p+32#64) 0x49 0xe9 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 32 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 36 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+36#64) 9#5 (.sib 4 none 0 (.d8 8))) from
    mov_m64_r64_effect_step (p+36#64) 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 36 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.2.1.scratch 8 8 (by decide) (by decide) (by decide)
    · x86_norm [BitVec.add_assoc]
      intro j hj k hk
      have h := hP.2.2 j hj (36+k) (by omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, stackPtr, Operand.read_reg64, BitVec.ofNat_eq_ofNat] using h
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.2.2
    · x86_norm [BitVec.add_assoc]
      exact next 41 (by decide) (by decide)
  advance_then (show StepEffect _ _ (leaR64Effect (p+41#64) 3#5 (.sib 4 none 0 (.d8 8))) from
    lea_r64_effect_step (p+41#64) 0x48 (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 41 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 46 (by decide) (by decide)
  advance_then (show StepEffect _ _ (xorR32R32Effect (p+46#64) 3 9#5 9#5) from
    xor_r32_r32_rex_effect_step (p+46#64) 0x45 0xc9 (by unfold RexNoWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 46 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 49 (by decide) (by decide)
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.Instructions.subR64M64Effect (p+49#64) 9#5 (.sib 4 none 0 (.d8 8))) from
    P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step (p+49#64) 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p borrowLowBytes 49 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.2.1.scratch 8 8 (by decide) (by decide) (by decide)).readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Field.Instructions.subR64M64Effect_components]
    · x86_norm [BitVec.add_assoc]
      exact next 54 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [borrowLowEffect, borrow, stackPtr, Operand.read_reg64, BitVec.xor_self, BitVec.zero_sub, BitVec.add_assoc]
    all_goals try (repeat constructor <;> rfl)
  · x86_norm [borrowLowEffect, borrow, stackPtr, Operand.read_reg64, BitVec.xor_self, BitVec.zero_sub, BitVec.add_assoc]
    all_goals try (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [borrowLowEffect, borrow, stackPtr, Operand.read_reg64, BitVec.xor_self, BitVec.zero_sub, BitVec.add_assoc]
    all_goals try (repeat constructor <;> rfl)
  · x86_norm [borrowLowEffect, borrow, stackPtr, Operand.read_reg64, BitVec.xor_self, BitVec.zero_sub, BitVec.add_assoc]
    all_goals try (repeat constructor <;> rfl)

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
