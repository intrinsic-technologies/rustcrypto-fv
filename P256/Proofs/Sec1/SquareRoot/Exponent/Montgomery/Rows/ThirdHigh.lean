import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Common

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64 mulM64Effect mul_m64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64R64Effect adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def thirdHighBytes : List UInt8 :=
  [0x4c, 0x89, 0xc8, 0x48, 0xf7, 0x64, 0x24, 0x40, 0x49, 0x89, 0xc2, 0x49, 0x89, 0xd1, 0x4d, 0x1, 0xf3, 0x4d, 0x11, 0xc2, 0x49, 0x83, 0xd1, 0x0, 0x49, 0x1, 0xf2, 0x49, 0x83, 0xd1, 0x0, 0x4d, 0x1, 0xe3, 0x49, 0x83, 0xd2, 0x0, 0x49, 0x83, 0xd1, 0x0]

def thirdHighEffect (p : BitVec 64) (s : RamState) : Effect :=
  let m1 := (((Operand.reg 9#5 : Operand 64).read s)*(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+64#64) : Operand 64).read s, mulHigh64 ((Operand.reg 9#5 : Operand 64).read s) ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+64#64) : Operand 64).read s))
  let a4 := addSpec (((Operand.reg 11#5 : Operand 64).read s)) (((Operand.reg 14#5 : Operand 64).read s))
  let c5 := adcSpec m1.1 (((Operand.reg 8#5 : Operand 64).read s)) (BitVec.ofBool a4.2.CF)
  let c6 := adcSpec m1.2 (0#64) (BitVec.ofBool c5.2.CF)
  let a7 := addSpec (c5.1) (((Operand.reg 6#5 : Operand 64).read s))
  let c8 := adcSpec c6.1 (0#64) (BitVec.ofBool a7.2.CF)
  let a9 := addSpec (a4.1) (((Operand.reg 12#5 : Operand 64).read s))
  let c10 := adcSpec a7.1 (0#64) (BitVec.ofBool a9.2.CF)
  let c11 := adcSpec c8.1 (0#64) (BitVec.ofBool c10.2.CF)
  { rip := p+42#64
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), m1.1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), m1.2⟩,
      ⟨(Operand.reg 10#5 : Operand 64), c10.1⟩,
      ⟨(Operand.reg 9#5 : Operand 64), c11.1⟩,
      ⟨(Operand.reg 11#5 : Operand 64), a9.1⟩]
    flags := some (.ofStatusFlags c11.2) }

theorem thirdHigh_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 42 → p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (BlockPre p 42) (codeRange p thirdHighBytes)
      (Effect.post (thirdHighEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect p 0#5 9#5) from
    mov_r64_r64_effect_step p 0x4c 0xc8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 0 3)
  try (case pre => intro s hP; exact hP.rip)
  case next =>
    intro s hP
    exact next 3 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulM64Effect (p+3#64) (.sib 4 none 0 (.d8 64))) from
    mul_m64_effect_step (p+3#64) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 3 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 64 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 8 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+8#64) 10#5 0#5) from
    mov_r64_r64_effect_step (p+8#64) 0x49 0xc2 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 8 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 11 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+11#64) 9#5 2#5) from
    mov_r64_r64_effect_step (p+11#64) 0x49 0xd1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 11 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 14 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+14#64) 11#5 14#5) from
    add_r64_r64_effect_step (p+14#64) 0x4d 0xf3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 14 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 17 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64R64Effect (p+17#64) 10#5 8#5) from
    adc_r64_r64_effect_step (p+17#64) 0x4d 0xc2 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 17 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 20 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+20#64) 9#5 0#8) from
    adc_r64_imm8_effect_step (p+20#64) 0x49 0xd1 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 20 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 24 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+24#64) 10#5 6#5) from
    add_r64_r64_effect_step (p+24#64) 0x49 0xf2 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 24 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 27 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+27#64) 9#5 0#8) from
    adc_r64_imm8_effect_step (p+27#64) 0x49 0xd1 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 27 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 31 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+31#64) 11#5 12#5) from
    add_r64_r64_effect_step (p+31#64) 0x4d 0xe3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 31 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 34 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+34#64) 10#5 0#8) from
    adc_r64_imm8_effect_step (p+34#64) 0x49 0xd2 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 34 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 38 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+38#64) 9#5 0#8) from
    adc_r64_imm8_effect_step (p+38#64) 0x49 0xd1 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdHighBytes 38 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 42 (by decide) (by decide)
  advance_finish [thirdHighEffect, addSpec_low, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
    restore_carry, BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]

theorem thirdHigh_bytes :
    Extracted.textBytes.toListFrom 0x148c8 thirdHighBytes.length = thirdHighBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
