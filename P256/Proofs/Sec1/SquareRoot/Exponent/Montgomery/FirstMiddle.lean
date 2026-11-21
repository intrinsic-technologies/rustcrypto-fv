import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstCarry

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64 mulR64Effect mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcSpec adc_r64_imm8_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def firstMiddleBytes : List UInt8 :=
  [0x49, 0x8b, 0x51, 0x10, 0x48, 0x89, 0x54, 0x24, 0x58, 0x4c, 0x89, 0xd8, 0x48, 0xf7, 0xe2, 0x48, 0x89, 0xc6, 0x49, 0x89, 0xd5, 0x48, 0x8b, 0x51, 0x10, 0x48, 0x89, 0x54, 0x24, 0x28, 0x4c, 0x89, 0xf0, 0x48, 0xf7, 0xe2, 0x49, 0x89, 0xd4, 0x48, 0x89, 0xc3, 0x4c, 0x1, 0xc3, 0x49, 0x83, 0xd4, 0x0, 0x48, 0x1, 0xeb, 0x49, 0x83, 0xd4, 0x0, 0x4d, 0x1, 0xfa, 0x4d, 0x8b, 0x41, 0x18, 0x48, 0x83, 0xd3, 0x0, 0x4c, 0x8b, 0x49, 0x18, 0x4c, 0x89, 0x4c, 0x24, 0x40, 0x49, 0x83, 0xd4, 0x0]

structure FirstMiddlePre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  memory : Reduction.MemoryPre s
  codeApart : RangeApart ((Operand.reg 4#5 : Operand 64).read s) 112 p firstMiddleBytes.length
  right : MemReadable s ((Operand.reg 9#5 : Operand 64).read s) 32
  rightApart : RangeApart ((Operand.reg 4#5 : Operand 64).read s) 112 ((Operand.reg 9#5 : Operand 64).read s) 32
  modulus : MemReadable s ((Operand.reg 1#5 : Operand 64).read s) 32
  modulusApart : RangeApart ((Operand.reg 4#5 : Operand 64).read s) 112 ((Operand.reg 1#5 : Operand 64).read s) 32

private theorem addSpec_low {n : Nat} (a b : BitVec n) : (addSpec a b).1 = a+b := rfl

def firstMiddleEffect (p : BitVec 64) (s : RamState) : Effect :=
  let l0 := (Operand.mem (((Operand.reg 9#5 : Operand 64).read s)+16#64) : Operand 64).read s
  let m3 := (((Operand.reg 11#5 : Operand 64).read s)*l0, mulHigh64 ((Operand.reg 11#5 : Operand 64).read s) l0)
  let l6 := (Operand.mem (((Operand.reg 1#5 : Operand 64).read s)+16#64) : Operand 64).read s
  let m9 := (((Operand.reg 14#5 : Operand 64).read s)*l6, mulHigh64 ((Operand.reg 14#5 : Operand 64).read s) l6)
  let a12 := addSpec m9.1 ((Operand.reg 8#5 : Operand 64).read s)
  let c13 := adcSpec m9.2 0#64 (BitVec.ofBool a12.2.CF)
  let a14 := addSpec a12.1 ((Operand.reg 5#5 : Operand 64).read s)
  let c15 := adcSpec c13.1 0#64 (BitVec.ofBool a14.2.CF)
  let a16 := addSpec ((Operand.reg 10#5 : Operand 64).read s) ((Operand.reg 15#5 : Operand 64).read s)
  let l17 := (Operand.mem (((Operand.reg 9#5 : Operand 64).read s)+24#64) : Operand 64).read s
  let c18 := adcSpec a14.1 0#64 (BitVec.ofBool a16.2.CF)
  let l19 := (Operand.mem (((Operand.reg 1#5 : Operand 64).read s)+24#64) : Operand 64).read s
  let c21 := adcSpec c15.1 0#64 (BitVec.ofBool c18.2.CF)
  { rip := p+80#64
    writes := [
      ⟨(Operand.reg 2#5 : Operand 64), m9.2⟩,
      ⟨(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+88#64) : Operand 64), l0⟩,
      ⟨(Operand.reg 0#5 : Operand 64), m9.1⟩,
      ⟨(Operand.reg 6#5 : Operand 64), m3.1⟩,
      ⟨(Operand.reg 13#5 : Operand 64), m3.2⟩,
      ⟨(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+40#64) : Operand 64), l6⟩,
      ⟨(Operand.reg 12#5 : Operand 64), c21.1⟩,
      ⟨(Operand.reg 3#5 : Operand 64), c18.1⟩,
      ⟨(Operand.reg 10#5 : Operand 64), a16.1⟩,
      ⟨(Operand.reg 8#5 : Operand 64), l17⟩,
      ⟨(Operand.reg 9#5 : Operand 64), l19⟩,
      ⟨(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+64#64) : Operand 64), l19⟩]
    flags := some (.ofStatusFlags c21.2) }

theorem firstMiddle_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 80 →
      p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (FirstMiddlePre p) (codeRange p firstMiddleBytes)
      (Effect.post (firstMiddleEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64M64Effect p 2#5 (.base 9 (.d8 16))) from
    mov_r64_m64_effect_step p 0x49 (by simp [RexWPrefix]) 2 (.base 9 (.d8 16)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 0 4)
  case pre =>
    intro s hP
    exact ⟨hP.rip, readable_limb hP.right 16 (by decide)⟩
  case next =>
    intro s hP
    exact next 4 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+4#64) 2#5 (.sib 4 none 0 (.d8 88))) from
    mov_m64_r64_effect_step (p+4#64) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 4 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 88 8 (by decide) (by decide) (by decide)
      · x86_norm
        intro i hi j hj
        have h := hP.codeApart (88+i) (by omega) (4+j) (by change 4+j < 80; omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 88 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 9 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+9#64) 0#5 11#5) from
    mov_r64_r64_effect_step (p+9#64) 0x4c 0xd8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 9 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 12 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulR64Effect (p+12#64) 2#5) from
    mul_r64_effect_step (p+12#64) 0x48 0xe2 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 12 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 15 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+15#64) 6#5 0#5) from
    mov_r64_r64_effect_step (p+15#64) 0x48 0xc6 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 15 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 18 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+18#64) 13#5 2#5) from
    mov_r64_r64_effect_step (p+18#64) 0x49 0xd5 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 18 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 21 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+21#64) 2#5 (.base 1 (.d8 16))) from
    mov_r64_m64_effect_step (p+21#64) 0x48 (by simp [RexWPrefix]) 2 (.base 1 (.d8 16)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 21 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact readable_limb hP.modulus 16 (by decide)
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 25 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+25#64) 2#5 (.sib 4 none 0 (.d8 40))) from
    mov_m64_r64_effect_step (p+25#64) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 25 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 40 8 (by decide) (by decide) (by decide)
      · x86_norm
        intro i hi j hj
        have h := hP.codeApart (40+i) (by omega) (25+j) (by change 25+j < 80; omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 40 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 30 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+30#64) 0#5 14#5) from
    mov_r64_r64_effect_step (p+30#64) 0x4c 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 30 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 33 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulR64Effect (p+33#64) 2#5) from
    mul_r64_effect_step (p+33#64) 0x48 0xe2 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 33 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 36 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+36#64) 12#5 2#5) from
    mov_r64_r64_effect_step (p+36#64) 0x49 0xd4 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 36 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 39 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+39#64) 3#5 0#5) from
    mov_r64_r64_effect_step (p+39#64) 0x48 0xc3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 39 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 42 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+42#64) 3#5 8#5) from
    add_r64_r64_effect_step (p+42#64) 0x4c 0xc3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 42 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 45 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+45#64) 12#5 0#8) from
    adc_r64_imm8_effect_step (p+45#64) 0x49 0xd4 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 45 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 49 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+49#64) 3#5 5#5) from
    add_r64_r64_effect_step (p+49#64) 0x48 0xeb (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 49 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 52 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+52#64) 12#5 0#8) from
    adc_r64_imm8_effect_step (p+52#64) 0x49 0xd4 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 52 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 56 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+56#64) 10#5 15#5) from
    add_r64_r64_effect_step (p+56#64) 0x4d 0xfa (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 56 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 59 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+59#64) 8#5 (.base 9 (.d8 24))) from
    mov_r64_m64_effect_step (p+59#64) 0x4d (by simp [RexWPrefix]) 0 (.base 9 (.d8 24)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 59 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact readable_limb hP.right 24 (by decide)
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 63 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+63#64) 3#5 0#8) from
    adc_r64_imm8_effect_step (p+63#64) 0x48 0xd3 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 63 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 67 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+67#64) 9#5 (.base 1 (.d8 24))) from
    mov_r64_m64_effect_step (p+67#64) 0x4c (by simp [RexWPrefix]) 1 (.base 1 (.d8 24)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 67 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact readable_limb hP.modulus 24 (by decide)
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 71 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+71#64) 9#5 (.sib 4 none 0 (.d8 64))) from
    mov_m64_r64_effect_step (p+71#64) 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 71 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 64 8 (by decide) (by decide) (by decide)
      · x86_norm
        intro i hi j hj
        have h := hP.codeApart (64+i) (by omega) (71+j) (by change 71+j < 80; omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 64 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 76 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+76#64) 12#5 0#8) from
    adc_r64_imm8_effect_step (p+76#64) 0x49 0xd4 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstMiddleBytes 76 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 80 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [firstMiddleEffect, BitVec.add_assoc]
  · simp (config := { decide := true }) (disch := decide +kernel) only
      [x86_compose, firstMiddleEffect, addSpec_low,
        scratch_load_store hP.rightApart, scratch_load_store hP.modulusApart]
    all_goals simp only [BitVec.add_assoc, BitVec.add_zero, and_self]
  · intro i
    cases i <;> simp (config := { decide := true }) (disch := decide +kernel) only
      [x86_compose, firstMiddleEffect, addSpec_low, BitVec.add_assoc,
        scratch_load_store hP.modulusApart]
  · x86_norm [firstMiddleEffect]

theorem firstMiddle_bytes :
    Extracted.textBytes.toListFrom 0x14670 firstMiddleBytes.length = firstMiddleBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery
