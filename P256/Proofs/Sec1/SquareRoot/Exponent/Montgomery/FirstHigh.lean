import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstMiddle

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64 mulR64Effect mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcSpec adc_r64_imm8_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def firstHighBytes : List UInt8 :=
  [0x4c, 0x89, 0xd8, 0x49, 0xf7, 0xe0, 0x4d, 0x89, 0xc3, 0x4c, 0x89, 0x44, 0x24, 0x60, 0x48, 0x89, 0xd1, 0x49, 0x89, 0xc0, 0x4c, 0x89, 0xf0, 0x49, 0xf7, 0xe1, 0x49, 0x89, 0xd1, 0x49, 0x89, 0xc7, 0x4d, 0x1, 0xef, 0x49, 0x83, 0xd1, 0x0, 0x4d, 0x1, 0xe7, 0x49, 0x83, 0xd1, 0x0, 0x48, 0x1, 0xf3, 0x49, 0x83, 0xd7, 0x0, 0x49, 0x83, 0xd1, 0x0]

structure FirstHighPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  memory : Reduction.MemoryPre s
  codeApart : RangeApart ((Operand.reg 4#5 : Operand 64).read s) 112 p firstHighBytes.length

private theorem addSpec_low {n : Nat} (a b : BitVec n) : (addSpec a b).1 = a+b := rfl

def firstHighEffect (p : BitVec 64) (s : RamState) : Effect :=
  let m1 := (((Operand.reg 11#5 : Operand 64).read s)*((Operand.reg 8#5 : Operand 64).read s), mulHigh64 ((Operand.reg 11#5 : Operand 64).read s) ((Operand.reg 8#5 : Operand 64).read s))
  let m7 := (((Operand.reg 14#5 : Operand 64).read s)*((Operand.reg 9#5 : Operand 64).read s), mulHigh64 ((Operand.reg 14#5 : Operand 64).read s) ((Operand.reg 9#5 : Operand 64).read s))
  let a10 := addSpec m7.1 ((Operand.reg 13#5 : Operand 64).read s)
  let c11 := adcSpec m7.2 0#64 (BitVec.ofBool a10.2.CF)
  let a12 := addSpec a10.1 ((Operand.reg 12#5 : Operand 64).read s)
  let c13 := adcSpec c11.1 0#64 (BitVec.ofBool a12.2.CF)
  let a14 := addSpec ((Operand.reg 3#5 : Operand 64).read s) ((Operand.reg 6#5 : Operand 64).read s)
  let c15 := adcSpec a12.1 0#64 (BitVec.ofBool a14.2.CF)
  let c16 := adcSpec c13.1 0#64 (BitVec.ofBool c15.2.CF)
  { rip := p+57#64
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), m7.1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), m7.2⟩,
      ⟨(Operand.reg 11#5 : Operand 64), ((Operand.reg 8#5 : Operand 64).read s)⟩,
      ⟨(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+96#64) : Operand 64), ((Operand.reg 8#5 : Operand 64).read s)⟩,
      ⟨(Operand.reg 1#5 : Operand 64), m1.2⟩,
      ⟨(Operand.reg 8#5 : Operand 64), m1.1⟩,
      ⟨(Operand.reg 9#5 : Operand 64), c16.1⟩,
      ⟨(Operand.reg 15#5 : Operand 64), c15.1⟩,
      ⟨(Operand.reg 3#5 : Operand 64), a14.1⟩]
    flags := some (.ofStatusFlags c16.2) }

theorem firstHigh_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 57 →
      p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (FirstHighPre p) (codeRange p firstHighBytes)
      (Effect.post (firstHighEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect p 0#5 11#5) from
    mov_r64_r64_effect_step p 0x4c 0xd8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 0 3)
  try (case pre => intro s hP; exact hP.rip)
  case next =>
    intro s hP
    exact next 3 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulR64Effect (p+3#64) 8#5) from
    mul_r64_effect_step (p+3#64) 0x49 0xe0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 3 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 6 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+6#64) 11#5 8#5) from
    mov_r64_r64_effect_step (p+6#64) 0x4d 0xc3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 6 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 9 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+9#64) 8#5 (.sib 4 none 0 (.d8 96))) from
    mov_m64_r64_effect_step (p+9#64) 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstHighBytes 9 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 96 8 (by decide) (by decide) (by decide)
      · x86_norm
        intro i hi j hj
        have h := hP.codeApart (96+i) (by omega) (9+j) (by change 9+j < 57; omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 96 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 14 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+14#64) 1#5 2#5) from
    mov_r64_r64_effect_step (p+14#64) 0x48 0xd1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 14 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 17 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+17#64) 8#5 0#5) from
    mov_r64_r64_effect_step (p+17#64) 0x49 0xc0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 17 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 20 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+20#64) 0#5 14#5) from
    mov_r64_r64_effect_step (p+20#64) 0x4c 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 20 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 23 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulR64Effect (p+23#64) 9#5) from
    mul_r64_effect_step (p+23#64) 0x49 0xe1 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 23 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 26 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+26#64) 9#5 2#5) from
    mov_r64_r64_effect_step (p+26#64) 0x49 0xd1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 26 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 29 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+29#64) 15#5 0#5) from
    mov_r64_r64_effect_step (p+29#64) 0x49 0xc7 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 29 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 32 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+32#64) 15#5 13#5) from
    add_r64_r64_effect_step (p+32#64) 0x4d 0xef (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 32 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 35 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+35#64) 9#5 0#8) from
    adc_r64_imm8_effect_step (p+35#64) 0x49 0xd1 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 35 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 39 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+39#64) 15#5 12#5) from
    add_r64_r64_effect_step (p+39#64) 0x4d 0xe7 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 39 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 42 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+42#64) 9#5 0#8) from
    adc_r64_imm8_effect_step (p+42#64) 0x49 0xd1 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 42 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 46 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+46#64) 3#5 6#5) from
    add_r64_r64_effect_step (p+46#64) 0x48 0xf3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 46 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 49 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+49#64) 15#5 0#8) from
    adc_r64_imm8_effect_step (p+49#64) 0x49 0xd7 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 49 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 53 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+53#64) 9#5 0#8) from
    adc_r64_imm8_effect_step (p+53#64) 0x49 0xd1 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstHighBytes 53 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 57 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [firstHighEffect, BitVec.add_assoc]
  · simp (config := { decide := true }) (disch := decide +kernel) only
      [x86_compose, firstHighEffect, addSpec_low,
        BitVec.add_assoc]
    all_goals simp only [BitVec.add_assoc, BitVec.add_zero, and_self]
  · intro i; cases i <;> x86_norm [firstHighEffect, addSpec_low, BitVec.add_assoc]
  · x86_norm [firstHighEffect]

theorem firstHigh_bytes :
    Extracted.textBytes.toListFrom 0x146c0 firstHighBytes.length = firstHighBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery
