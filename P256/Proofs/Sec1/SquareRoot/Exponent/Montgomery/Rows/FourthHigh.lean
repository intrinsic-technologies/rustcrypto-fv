import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Common

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64 mulR64Effect mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64R64Effect adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def fourthHighBytes : List UInt8 :=
  [0x4c, 0x89, 0xf8, 0x4c, 0x8b, 0x64, 0x24, 0x40, 0x49, 0xf7, 0xe4, 0x4c, 0x1, 0xd6, 0x4c, 0x11, 0xe8, 0x48, 0x83, 0xd2, 0x0, 0x48, 0x1, 0xe8, 0x48, 0x83, 0xd2, 0x0, 0x48, 0x1, 0xde, 0x48, 0x83, 0xd0, 0x0, 0x48, 0x83, 0xd2, 0x0]

def fourthHighEffect (p : BitVec 64) (s : RamState) : Effect :=
  let l1 := (Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+64#64) : Operand 64).read s
  let m2 := (((Operand.reg 15#5 : Operand 64).read s)*l1, mulHigh64 ((Operand.reg 15#5 : Operand 64).read s) (l1))
  let a3 := addSpec (((Operand.reg 6#5 : Operand 64).read s)) (((Operand.reg 10#5 : Operand 64).read s))
  let c4 := adcSpec m2.1 (((Operand.reg 13#5 : Operand 64).read s)) (BitVec.ofBool a3.2.CF)
  let c5 := adcSpec m2.2 (0#64) (BitVec.ofBool c4.2.CF)
  let a6 := addSpec (c4.1) (((Operand.reg 5#5 : Operand 64).read s))
  let c7 := adcSpec c5.1 (0#64) (BitVec.ofBool a6.2.CF)
  let a8 := addSpec (a3.1) (((Operand.reg 3#5 : Operand 64).read s))
  let c9 := adcSpec a6.1 (0#64) (BitVec.ofBool a8.2.CF)
  let c10 := adcSpec c7.1 (0#64) (BitVec.ofBool c9.2.CF)
  { rip := p+39#64
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), c9.1⟩,
      ⟨(Operand.reg 12#5 : Operand 64), l1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), c10.1⟩,
      ⟨(Operand.reg 6#5 : Operand 64), a8.1⟩]
    flags := some (.ofStatusFlags c10.2) }

theorem fourthHigh_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 39 → p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (BlockPre p 39) (codeRange p fourthHighBytes)
      (Effect.post (fourthHighEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect p 0#5 15#5) from
    mov_r64_r64_effect_step p 0x4c 0xf8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthHighBytes 0 3)
  try (case pre => intro s hP; exact hP.rip)
  case next =>
    intro s hP
    exact next 3 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+3#64) 12#5 (.sib 4 none 0 (.d8 64))) from
    mov_r64_m64_effect_step (p+3#64) 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p fourthHighBytes 3 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 64 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 8 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulR64Effect (p+8#64) 12#5) from
    mul_r64_effect_step (p+8#64) 0x49 0xe4 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthHighBytes 8 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 11 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+11#64) 6#5 10#5) from
    add_r64_r64_effect_step (p+11#64) 0x4c 0xd6 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthHighBytes 11 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 14 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64R64Effect (p+14#64) 0#5 13#5) from
    adc_r64_r64_effect_step (p+14#64) 0x4c 0xe8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthHighBytes 14 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 17 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+17#64) 2#5 0#8) from
    adc_r64_imm8_effect_step (p+17#64) 0x48 0xd2 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthHighBytes 17 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 21 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+21#64) 0#5 5#5) from
    add_r64_r64_effect_step (p+21#64) 0x48 0xe8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthHighBytes 21 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 24 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+24#64) 2#5 0#8) from
    adc_r64_imm8_effect_step (p+24#64) 0x48 0xd2 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthHighBytes 24 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 28 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+28#64) 6#5 3#5) from
    add_r64_r64_effect_step (p+28#64) 0x48 0xde (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthHighBytes 28 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 31 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+31#64) 0#5 0#8) from
    adc_r64_imm8_effect_step (p+31#64) 0x48 0xd0 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthHighBytes 31 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 35 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+35#64) 2#5 0#8) from
    adc_r64_imm8_effect_step (p+35#64) 0x48 0xd2 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthHighBytes 35 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 39 (by decide) (by decide)
  advance_finish [fourthHighEffect, addSpec_low, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
    restore_carry, BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]

theorem fourthHigh_bytes :
    Extracted.textBytes.toListFrom 0x149c9 fourthHighBytes.length = fourthHighBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
