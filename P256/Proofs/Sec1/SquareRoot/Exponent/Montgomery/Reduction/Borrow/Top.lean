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

def borrowTopBytes : List UInt8 :=
  [0x49, 0x89, 0xd5, 0x4d, 0x29, 0xe5, 0x49, 0xc1, 0xfe, 0x3f, 0x4d, 0x1, 0xee, 0x49, 0x89, 0xd5, 0x49, 0xf7, 0xd5, 0x4c, 0x89, 0xe5, 0x4c, 0x21, 0xed, 0x4d, 0x9, 0xe5, 0x4d, 0x21, 0xf5, 0x49, 0x9, 0xed, 0x49, 0xc1, 0xed, 0x3f, 0x4c, 0x89, 0x6c, 0x24, 0x8, 0x45, 0x31, 0xed, 0x4c, 0x2b, 0x6c, 0x24, 0x8]

def borrowTopEffect (p : BitVec 64) (s : RamState) : Effect :=
  let a := (Operand.reg 2#5 : Operand 64).read s
  let m := (Operand.reg 12#5 : Operand 64).read s
  let r := ((Operand.reg 14#5 : Operand 64).read s).sshiftRight 63 + (a-m)
  let b := borrow a m r
  { rip := p+51#64
    writes := [⟨(Operand.reg 14#5 : Operand 64), r⟩,
      ⟨(Operand.reg 13#5 : Operand 64), -b⟩,
      ⟨(Operand.reg 5#5 : Operand 64), m &&& ~~~a⟩,
      ⟨(Operand.mem (stackPtr s+8#64) : Operand 64), b⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem borrow_top_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 51 →
      p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p ∧ MemoryPre s ∧
      RangeApart (stackPtr s+8#64) 8 p 51)
      (codeRange p borrowTopBytes) (Effect.post (borrowTopEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect p 13#5 2#5) from
    mov_r64_r64_effect_step p 0x49 0xd5 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 0 3)
  case next =>
    intro s hP
    exact next 3 (by decide) (by decide)
  advance_then (show StepEffect _ _ (subR64R64Effect (p+3#64) 13#5 12#5) from
    sub_r64_r64_effect_step (p+3#64) 0x4d 0xe5 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 3 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 6 (by decide) (by decide)
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.sarR64Effect (p+6#64) 4 14#5 63) from
    P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step (p+6#64) 0x49 0xfe 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 6 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Instructions.sarR64Effect_components]
    · x86_norm [BitVec.add_assoc]
      exact next 10 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+10#64) 14#5 13#5) from
    add_r64_r64_effect_step (p+10#64) 0x4d 0xee (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 10 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 13 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+13#64) 13#5 2#5) from
    mov_r64_r64_effect_step (p+13#64) 0x49 0xd5 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 13 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 16 (by decide) (by decide)
  advance_then (show StepEffect _ _ (notR64Effect (p+16#64) 13#5) from
    not_r64_effect_step (p+16#64) 0x49 0xd5 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 16 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 19 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+19#64) 5#5 12#5) from
    mov_r64_r64_effect_step (p+19#64) 0x4c 0xe5 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 19 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 22 (by decide) (by decide)
  advance_then (show StepEffect _ _ (andR64R64Effect (p+22#64) 5#5 13#5) from
    and_r64_r64_effect_step (p+22#64) 0x4c 0xed (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 22 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 25 (by decide) (by decide)
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.FieldNeg.Instructions.orR64R64Effect (p+25#64) 13#5 12#5) from
    P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step (p+25#64) 0x4d 0xe5 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 25 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 28 (by decide) (by decide)
  advance_then (show StepEffect _ _ (andR64R64Effect (p+28#64) 13#5 14#5) from
    and_r64_r64_effect_step (p+28#64) 0x4d 0xf5 (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 28 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 31 (by decide) (by decide)
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.FieldNeg.Instructions.orR64R64Effect (p+31#64) 13#5 5#5) from
    P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step (p+31#64) 0x49 0xed (by unfold RexWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 31 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 34 (by decide) (by decide)
  advance_then (show StepEffect _ _ (shrR64Effect (p+34#64) 4 13#5 63) from
    shr_r64_imm8_effect_step (p+34#64) 0x49 0xed 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 34 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 38 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+38#64) 13#5 (.sib 4 none 0 (.d8 8))) from
    mov_m64_r64_effect_step (p+38#64) 0x4c (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 38 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.2.1.scratch 8 8 (by decide) (by decide) (by decide)
    · x86_norm [BitVec.add_assoc]
      intro j hj k hk
      have h := hP.2.2 j hj (38+k) (by omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, stackPtr, Operand.read_reg64, BitVec.ofNat_eq_ofNat] using h
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.2.2
    · x86_norm [BitVec.add_assoc]
      exact next 43 (by decide) (by decide)
  advance_then (show StepEffect _ _ (xorR32R32Effect (p+43#64) 3 13#5 13#5) from
    xor_r32_r32_rex_effect_step (p+43#64) 0x45 0xed (by unfold RexNoWPrefix; decide +kernel) rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 43 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm [BitVec.add_assoc]
      exact next 46 (by decide) (by decide)
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.Instructions.subR64M64Effect (p+46#64) 13#5 (.sib 4 none 0 (.d8 8))) from
    P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step (p+46#64) 0x4c (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p borrowTopBytes 46 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.2.1.scratch 8 8 (by decide) (by decide) (by decide)).readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers, P256.Proofs.Common.Field.Instructions.subR64M64Effect_components]
    · x86_norm [BitVec.add_assoc]
      exact next 51 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [borrowTopEffect, borrow, stackPtr, Operand.read_reg64, BitVec.xor_self, BitVec.zero_sub, BitVec.add_assoc]
    all_goals try (repeat constructor <;> rfl)
  · x86_norm [borrowTopEffect, borrow, stackPtr, Operand.read_reg64, BitVec.xor_self, BitVec.zero_sub, BitVec.add_assoc]
    all_goals try (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [borrowTopEffect, borrow, stackPtr, Operand.read_reg64, BitVec.xor_self, BitVec.zero_sub, BitVec.add_assoc]
    all_goals try (repeat constructor <;> rfl)
  · x86_norm [borrowTopEffect, borrow, stackPtr, Operand.read_reg64, BitVec.xor_self, BitVec.zero_sub, BitVec.add_assoc]
    all_goals try (repeat constructor <;> rfl)

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
