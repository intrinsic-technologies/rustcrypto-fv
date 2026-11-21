import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Common

set_option autoImplicit false

open P256.Proofs.Common.Instructions (addR64M64Effect add_r64_m64_effect_step mulHigh64 mulM64Effect mul_m64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64R64Effect adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def thirdMiddleBytes : List UInt8 :=
  [0x4c, 0x89, 0xe0, 0x48, 0xf7, 0x64, 0x24, 0x58, 0x49, 0x89, 0xd0, 0x49, 0x89, 0xc3, 0x4c, 0x89, 0xc8, 0x48, 0xf7, 0x64, 0x24, 0x28, 0x49, 0x89, 0xc4, 0x48, 0x89, 0xd6, 0x48, 0x3, 0x5c, 0x24, 0x38, 0x4d, 0x11, 0xd4, 0x48, 0x83, 0xd6, 0x0, 0x4d, 0x1, 0xec, 0x48, 0x83, 0xd6, 0x0, 0x48, 0x1, 0xeb, 0x49, 0x83, 0xd4, 0x0, 0x48, 0x83, 0xd6, 0x0]

def thirdMiddleEffect (p : BitVec 64) (s : RamState) : Effect :=
  let m1 := (((Operand.reg 12#5 : Operand 64).read s)*(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+88#64) : Operand 64).read s, mulHigh64 ((Operand.reg 12#5 : Operand 64).read s) ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+88#64) : Operand 64).read s))
  let m5 := (((Operand.reg 9#5 : Operand 64).read s)*(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+40#64) : Operand 64).read s, mulHigh64 ((Operand.reg 9#5 : Operand 64).read s) ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+40#64) : Operand 64).read s))
  let a8 := addSpec (((Operand.reg 3#5 : Operand 64).read s)) ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+56#64) : Operand 64).read s)
  let c9 := adcSpec m5.1 (((Operand.reg 10#5 : Operand 64).read s)) (BitVec.ofBool a8.2.CF)
  let c10 := adcSpec m5.2 (0#64) (BitVec.ofBool c9.2.CF)
  let a11 := addSpec (c9.1) (((Operand.reg 13#5 : Operand 64).read s))
  let c12 := adcSpec c10.1 (0#64) (BitVec.ofBool a11.2.CF)
  let a13 := addSpec (a8.1) (((Operand.reg 5#5 : Operand 64).read s))
  let c14 := adcSpec a11.1 (0#64) (BitVec.ofBool a13.2.CF)
  let c15 := adcSpec c12.1 (0#64) (BitVec.ofBool c14.2.CF)
  { rip := p+58#64
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), m5.1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), m5.2⟩,
      ⟨(Operand.reg 8#5 : Operand 64), m1.2⟩,
      ⟨(Operand.reg 11#5 : Operand 64), m1.1⟩,
      ⟨(Operand.reg 12#5 : Operand 64), c14.1⟩,
      ⟨(Operand.reg 6#5 : Operand 64), c15.1⟩,
      ⟨(Operand.reg 3#5 : Operand 64), a13.1⟩]
    flags := some (.ofStatusFlags c15.2) }

theorem thirdMiddle_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 58 → p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (BlockPre p 58) (codeRange p thirdMiddleBytes)
      (Effect.post (thirdMiddleEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect p 0#5 12#5) from
    mov_r64_r64_effect_step p 0x4c 0xe0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 0 3)
  try (case pre => intro s hP; exact hP.rip)
  case next =>
    intro s hP
    exact next 3 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulM64Effect (p+3#64) (.sib 4 none 0 (.d8 88))) from
    mul_m64_effect_step (p+3#64) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 3 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 88 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 8 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+8#64) 8#5 2#5) from
    mov_r64_r64_effect_step (p+8#64) 0x49 0xd0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 8 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 11 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+11#64) 11#5 0#5) from
    mov_r64_r64_effect_step (p+11#64) 0x49 0xc3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 11 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 14 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+14#64) 0#5 9#5) from
    mov_r64_r64_effect_step (p+14#64) 0x4c 0xc8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 14 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 17 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulM64Effect (p+17#64) (.sib 4 none 0 (.d8 40))) from
    mul_m64_effect_step (p+17#64) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 17 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 40 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 22 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+22#64) 12#5 0#5) from
    mov_r64_r64_effect_step (p+22#64) 0x49 0xc4 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 22 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 25 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+25#64) 6#5 2#5) from
    mov_r64_r64_effect_step (p+25#64) 0x48 0xd6 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 25 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 28 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64M64Effect (p+28#64) 3#5 (.sib 4 none 0 (.d8 56))) from
    add_r64_m64_effect_step (p+28#64) 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 28 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 56 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 33 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64R64Effect (p+33#64) 12#5 10#5) from
    adc_r64_r64_effect_step (p+33#64) 0x4d 0xd4 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 33 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 36 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+36#64) 6#5 0#8) from
    adc_r64_imm8_effect_step (p+36#64) 0x48 0xd6 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 36 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 40 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+40#64) 12#5 13#5) from
    add_r64_r64_effect_step (p+40#64) 0x4d 0xec (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 40 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 43 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+43#64) 6#5 0#8) from
    adc_r64_imm8_effect_step (p+43#64) 0x48 0xd6 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 43 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 47 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+47#64) 3#5 5#5) from
    add_r64_r64_effect_step (p+47#64) 0x48 0xeb (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 47 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 50 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+50#64) 12#5 0#8) from
    adc_r64_imm8_effect_step (p+50#64) 0x49 0xd4 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 50 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 54 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+54#64) 6#5 0#8) from
    adc_r64_imm8_effect_step (p+54#64) 0x48 0xd6 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdMiddleBytes 54 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 58 (by decide) (by decide)
  advance_finish [thirdMiddleEffect, addSpec_low, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
    restore_carry, BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]

theorem thirdMiddle_bytes :
    Extracted.textBytes.toListFrom 0x1488e thirdMiddleBytes.length = thirdMiddleBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
