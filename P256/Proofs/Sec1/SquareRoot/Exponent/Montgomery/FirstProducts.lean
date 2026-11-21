import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Initialize
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (imulR64R64Effect imul_r64_r64_effect_step mulFlags64 mulHigh64 mulR64Effect mul_r64_effect_step)

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def firstProductsBytes : List UInt8 :=
  [0x4c, 0x89, 0xd8, 0x48, 0xf7, 0xe2, 0x48, 0x89, 0xc6, 0x48, 0x89, 0xd3, 0x4c, 0xf, 0xaf, 0xf0, 0x4c, 0x89, 0xf0, 0x49, 0xf7, 0xe7, 0x49, 0x89, 0xd4, 0x49, 0x89, 0xc5, 0x4c, 0x89, 0xd8, 0x49, 0xf7, 0xe2, 0x49, 0x89, 0xc7, 0x49, 0x89, 0xd0]

def firstProductsEffect (p : BitVec 64) (s : RamState) : Effect :=
  let a0 := (Operand.reg 11#5 : Operand 64).read s
  let b0 := (Operand.reg 2#5 : Operand 64).read s
  let b1 := (Operand.reg 10#5 : Operand 64).read s
  let p0 := (Operand.reg 15#5 : Operand 64).read s
  let q := (Operand.reg 14#5 : Operand 64).read s * (a0*b0)
  { rip := p+40#64
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), a0*b1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), mulHigh64 a0 b1⟩,
      ⟨(Operand.reg 6#5 : Operand 64), a0*b0⟩,
      ⟨(Operand.reg 3#5 : Operand 64), mulHigh64 a0 b0⟩,
      ⟨(Operand.reg 14#5 : Operand 64), q⟩,
      ⟨(Operand.reg 12#5 : Operand 64), mulHigh64 q p0⟩,
      ⟨(Operand.reg 13#5 : Operand 64), q*p0⟩,
      ⟨(Operand.reg 15#5 : Operand 64), a0*b1⟩,
      ⟨(Operand.reg 8#5 : Operand 64), mulHigh64 a0 b1⟩]
    flags := some (mulFlags64 a0 b1) }

theorem firstProducts_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 40 →
      p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p firstProductsBytes)
      (Effect.post (firstProductsEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect p 0#5 11#5) from
    mov_r64_r64_effect_step p 0x4c 0xd8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 0 3)
  case next =>
    intro s hP
    exact next 3 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulR64Effect (p+3#64) 2#5) from
    mul_r64_effect_step (p+3#64) 0x48 0xe2 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 3 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 6 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+6#64) 6#5 0#5) from
    mov_r64_r64_effect_step (p+6#64) 0x48 0xc6 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 6 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 9 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+9#64) 3#5 2#5) from
    mov_r64_r64_effect_step (p+9#64) 0x48 0xd3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 9 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 12 (by decide) (by decide)
  advance_then (show StepEffect _ _ (imulR64R64Effect (p+12#64) 14#5 0#5) from
    imul_r64_r64_effect_step (p+12#64) 0x4c 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 12 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 16 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+16#64) 0#5 14#5) from
    mov_r64_r64_effect_step (p+16#64) 0x4c 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 16 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 19 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulR64Effect (p+19#64) 15#5) from
    mul_r64_effect_step (p+19#64) 0x49 0xe7 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 19 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 22 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+22#64) 12#5 2#5) from
    mov_r64_r64_effect_step (p+22#64) 0x49 0xd4 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 22 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 25 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+25#64) 13#5 0#5) from
    mov_r64_r64_effect_step (p+25#64) 0x49 0xc5 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 25 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 28 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+28#64) 0#5 11#5) from
    mov_r64_r64_effect_step (p+28#64) 0x4c 0xd8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 28 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 31 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulR64Effect (p+31#64) 10#5) from
    mul_r64_effect_step (p+31#64) 0x49 0xe2 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 31 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 34 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+34#64) 15#5 0#5) from
    mov_r64_r64_effect_step (p+34#64) 0x49 0xc7 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 34 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 37 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+37#64) 8#5 2#5) from
    mov_r64_r64_effect_step (p+37#64) 0x49 0xd0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstProductsBytes 37 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 40 (by decide) (by decide)
  advance_finish [firstProductsEffect, BitVec.add_assoc]

theorem firstProducts_bytes :
    Extracted.textBytes.toListFrom 0x1461a firstProductsBytes.length = firstProductsBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery
