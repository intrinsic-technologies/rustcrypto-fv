import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Common

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64 mulM64Effect mul_m64_effect_step)
open P256.Proofs.Common.Instructions.AddByte (addR8Imm8LegacyEffect add_r8_imm8_legacy_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64R64Effect adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccM8Effect setccR8Effect setcc_m8_effect_step setcc_r8_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def thirdTopBytes : List UInt8 :=
  [0x4d, 0x1, 0xf9, 0x44, 0xf, 0xb6, 0x44, 0x24, 0x7, 0x49, 0x83, 0xd0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x70, 0x18, 0x48, 0x89, 0xf0, 0x48, 0xf7, 0x64, 0x24, 0x60, 0x49, 0x89, 0xd6, 0x49, 0x1, 0xca, 0x49, 0x83, 0xd1, 0x0, 0xf, 0x92, 0xc1, 0x49, 0x1, 0xc1, 0x49, 0x83, 0xd6, 0x0, 0x80, 0xc1, 0xff, 0x4d, 0x11, 0xc6, 0xf, 0x92, 0x44, 0x24, 0x18]

def thirdTopEffect (p : BitVec 64) (s : RamState) : Effect :=
  let a0 := addSpec (((Operand.reg 9#5 : Operand 64).read s)) (((Operand.reg 15#5 : Operand 64).read s))
  let l1 := ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+7#64) : Operand 8).read s).setWidth 64
  let c2 := adcSpec l1 (0#64) (BitVec.ofBool a0.2.CF)
  let l3 := (Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+24#64) : Operand 64).read s
  let l4 := (Operand.mem (l3+24#64) : Operand 64).read s
  let m6 := (l4*(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+96#64) : Operand 64).read s, mulHigh64 l4 ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+96#64) : Operand 64).read s))
  let a8 := addSpec (((Operand.reg 10#5 : Operand 64).read s)) (((Operand.reg 1#5 : Operand 64).read s))
  let c9 := adcSpec (((Operand.reg 9#5 : Operand 64).read s)+((Operand.reg 15#5 : Operand 64).read s)) (0#64) (BitVec.ofBool a8.2.CF)
  let a11 := addSpec (c9.1) (m6.1)
  let c12 := adcSpec m6.2 (0#64) (BitVec.ofBool a11.2.CF)
  let a13 := addSpec ((mergeGPR 8 (if c9.2.CF then 1#8 else 0#8) ((Operand.reg 1#5 : Operand 64).read s)).setWidth 8) (255#8)
  let c14 := adcSpec c12.1 (c2.1) (BitVec.ofBool a13.2.CF)
  { rip := p+61#64
    writes := [
      ⟨(Operand.reg 8#5 : Operand 64), c2.1⟩,
      ⟨(Operand.reg 6#5 : Operand 64), l4⟩,
      ⟨(Operand.reg 0#5 : Operand 64), m6.1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), m6.2⟩,
      ⟨(Operand.reg 10#5 : Operand 64), (((Operand.reg 10#5 : Operand 64).read s)+((Operand.reg 1#5 : Operand 64).read s))⟩,
      ⟨(Operand.reg 9#5 : Operand 64), (c9.1+m6.1)⟩,
      ⟨(Operand.reg 1#5 : Operand 64), mergeGPR 8 ((mergeGPR 8 (if c9.2.CF then 1#8 else 0#8) ((Operand.reg 1#5 : Operand 64).read s)).setWidth 8+255#8) (mergeGPR 8 (if c9.2.CF then 1#8 else 0#8) ((Operand.reg 1#5 : Operand 64).read s))⟩,
      ⟨(Operand.reg 14#5 : Operand 64), c14.1⟩,
      ⟨(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+24#64) : Operand 8), (if c14.2.CF then 1#8 else 0#8)⟩]
    flags := some (.ofStatusFlags c14.2) }

theorem thirdTop_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 61 → p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (TopPre p 61) (codeRange p thirdTopBytes)
      (Effect.post (thirdTopEffect p)) := by
  advance_begin (show StepEffect _ _ (addR64R64Effect p 9#5 15#5) from
    add_r64_r64_effect_step p 0x4d 0xf9 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 0 3)
  try (case pre => intro s hP; exact hP.rip)
  case next =>
    intro s hP
    exact next 3 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movzxR32M8Effect (p+3#64) 6 8#5 (.sib 4 none 0 (.d8 7))) from
    movzx_r_m8_rex_effect_step (p+3#64) 0x44 (by simp [RexPrefix]) 32 (by right; rfl) (by intro seg; rfl) 0 (.sib 4 none 0 (.d8 7)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 3 6)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (scratch_byte_writable hP.memory 7 (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 9 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+9#64) 8#5 0#8) from
    adc_r64_imm8_effect_step (p+9#64) 0x49 0xd0 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 9 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 13 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+13#64) 0#5 (.sib 4 none 0 (.d8 24))) from
    mov_r64_m64_effect_step (p+13#64) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 13 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 24 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 18 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+18#64) 6#5 (.base 0 (.d8 24))) from
    mov_r64_m64_effect_step (p+18#64) 0x48 (by simp [RexWPrefix]) 6 (.base 0 (.d8 24)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 18 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact readable_limb hP.input 24 (by decide)
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 22 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+22#64) 0#5 6#5) from
    mov_r64_r64_effect_step (p+22#64) 0x48 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 22 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 25 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulM64Effect (p+25#64) (.sib 4 none 0 (.d8 96))) from
    mul_m64_effect_step (p+25#64) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 25 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 96 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 30 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+30#64) 14#5 2#5) from
    mov_r64_r64_effect_step (p+30#64) 0x49 0xd6 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 30 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 33 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+33#64) 10#5 1#5) from
    add_r64_r64_effect_step (p+33#64) 0x49 0xca (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 33 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 36 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+36#64) 9#5 0#8) from
    adc_r64_imm8_effect_step (p+36#64) 0x49 0xd1 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 36 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 40 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (setccR8Effect (p+40#64) 3 1#5 2#4) from
    setcc_r8_effect_step (p+40#64) 0x92 0xc1 (by left; rfl) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 40 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 43 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+43#64) 9#5 0#5) from
    add_r64_r64_effect_step (p+43#64) 0x49 0xc1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 43 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 46 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+46#64) 14#5 0#8) from
    adc_r64_imm8_effect_step (p+46#64) 0x49 0xd6 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 46 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 50 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR8Imm8LegacyEffect (p+50#64) 1#5 255#8) from
    add_r8_imm8_legacy_effect_step (p+50#64) 0xc1 255 (by decide) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 50 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 53 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64R64Effect (p+53#64) 14#5 8#5) from
    adc_r64_r64_effect_step (p+53#64) 0x4d 0xc6 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 53 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 56 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (setccM8Effect (p+56#64) 5 (.sib 4 none 0 (.d8 24)) 2#4) from
    setcc_m8_effect_step (p+56#64) 0x92 (by left; rfl) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p thirdTopBytes 56 5)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact scratch_byte_writable hP.memory 24 (by decide)
      · x86_norm
        intro i hi j hj
        have h := hP.codeApart (24+i) (by omega) (56+j) (by omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 24 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 61 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [thirdTopEffect, BitVec.add_assoc]
  · x86_norm [thirdTopEffect, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
      restore_carry, BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
    all_goals try simp only [eq_self, or_true, true_or]
  · intro i
    cases i <;> x86_norm [thirdTopEffect, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
      restore_carry, BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
  · x86_norm [thirdTopEffect]

theorem thirdTop_bytes :
    Extracted.textBytes.toListFrom 0x148f2 thirdTopBytes.length = thirdTopBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
