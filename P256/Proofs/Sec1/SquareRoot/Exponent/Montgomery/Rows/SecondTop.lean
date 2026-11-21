import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Common

set_option autoImplicit false

open P256.Proofs.Common.Instructions (addR64M64Effect add_r64_m64_effect_step mulHigh64 mulM64Effect mul_m64_effect_step)
open P256.Proofs.Common.Instructions.AddByte (addR8Imm8LegacyEffect add_r8_imm8_legacy_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64R64Effect adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccM8Effect setccR8Effect setcc_m8_effect_step setcc_r8_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def secondTopBytes : List UInt8 :=
  [0x48, 0x3, 0x4c, 0x24, 0x68, 0xf, 0xb6, 0x74, 0x24, 0x7, 0x48, 0x83, 0xd6, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x4c, 0x8b, 0x60, 0x10, 0x4c, 0x89, 0xe0, 0x48, 0xf7, 0x64, 0x24, 0x60, 0x49, 0x89, 0xd7, 0x4d, 0x1, 0xce, 0x48, 0x83, 0xd1, 0x0, 0xf, 0x92, 0xc2, 0x48, 0x1, 0xc1, 0x49, 0x83, 0xd7, 0x0, 0x80, 0xc2, 0xff, 0x49, 0x11, 0xf7, 0xf, 0x92, 0x44, 0x24, 0x7]

def secondTopEffect (p : BitVec 64) (s : RamState) : Effect :=
  let a0 := addSpec (((Operand.reg 1#5 : Operand 64).read s)) ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+104#64) : Operand 64).read s)
  let l1 := ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+7#64) : Operand 8).read s).setWidth 64
  let c2 := adcSpec l1 (0#64) (BitVec.ofBool a0.2.CF)
  let l3 := (Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+24#64) : Operand 64).read s
  let l4 := (Operand.mem (l3+16#64) : Operand 64).read s
  let m6 := (l4*(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+96#64) : Operand 64).read s, mulHigh64 l4 ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+96#64) : Operand 64).read s))
  let a8 := addSpec (((Operand.reg 14#5 : Operand 64).read s)) (((Operand.reg 9#5 : Operand 64).read s))
  let c9 := adcSpec (((Operand.reg 1#5 : Operand 64).read s)+(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+104#64) : Operand 64).read s) (0#64) (BitVec.ofBool a8.2.CF)
  let a11 := addSpec (c9.1) (m6.1)
  let c12 := adcSpec m6.2 (0#64) (BitVec.ofBool a11.2.CF)
  let a13 := addSpec ((mergeGPR 8 (if c9.2.CF then 1#8 else 0#8) m6.2).setWidth 8) (255#8)
  let c14 := adcSpec c12.1 (c2.1) (BitVec.ofBool a13.2.CF)
  { rip := p+62#64
    writes := [
      ⟨(Operand.reg 6#5 : Operand 64), c2.1⟩,
      ⟨(Operand.reg 12#5 : Operand 64), l4⟩,
      ⟨(Operand.reg 0#5 : Operand 64), m6.1⟩,
      ⟨(Operand.reg 14#5 : Operand 64), (((Operand.reg 14#5 : Operand 64).read s)+((Operand.reg 9#5 : Operand 64).read s))⟩,
      ⟨(Operand.reg 1#5 : Operand 64), (c9.1+m6.1)⟩,
      ⟨(Operand.reg 2#5 : Operand 64), mergeGPR 8 ((mergeGPR 8 (if c9.2.CF then 1#8 else 0#8) m6.2).setWidth 8+255#8) (mergeGPR 8 (if c9.2.CF then 1#8 else 0#8) m6.2)⟩,
      ⟨(Operand.reg 15#5 : Operand 64), c14.1⟩,
      ⟨(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+7#64) : Operand 8), (if c14.2.CF then 1#8 else 0#8)⟩]
    flags := some (.ofStatusFlags c14.2) }

theorem secondTop_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 62 → p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (TopPre p 62) (codeRange p secondTopBytes)
      (Effect.post (secondTopEffect p)) := by
  advance_begin (show StepEffect _ _ (addR64M64Effect p 1#5 (.sib 4 none 0 (.d8 104))) from
    add_r64_m64_effect_step p 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p secondTopBytes 0 5)
  try (case pre => intro s hP; exact hP.rip)
  case pre =>
    intro s hP
    exact ⟨hP.rip, (hP.memory.scratch 104 8 (by decide) (by decide) (by decide)).readable⟩
  case next =>
    intro s hP
    exact next 5 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movzxR32M8Effect (p+5#64) 5 6#5 (.sib 4 none 0 (.d8 7))) from
    movzx_r32_m8_effect_step (p+5#64) 6 (.sib 4 none 0 (.d8 7)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p secondTopBytes 5 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (scratch_byte_writable hP.memory 7 (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 10 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+10#64) 6#5 0#8) from
    adc_r64_imm8_effect_step (p+10#64) 0x48 0xd6 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p secondTopBytes 10 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 14 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+14#64) 0#5 (.sib 4 none 0 (.d8 24))) from
    mov_r64_m64_effect_step (p+14#64) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p secondTopBytes 14 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 24 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 19 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+19#64) 12#5 (.base 0 (.d8 16))) from
    mov_r64_m64_effect_step (p+19#64) 0x4c (by simp [RexWPrefix]) 4 (.base 0 (.d8 16)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p secondTopBytes 19 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact readable_limb hP.input 16 (by decide)
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 23 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+23#64) 0#5 12#5) from
    mov_r64_r64_effect_step (p+23#64) 0x4c 0xe0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p secondTopBytes 23 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 26 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulM64Effect (p+26#64) (.sib 4 none 0 (.d8 96))) from
    mul_m64_effect_step (p+26#64) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p secondTopBytes 26 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 96 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 31 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+31#64) 15#5 2#5) from
    mov_r64_r64_effect_step (p+31#64) 0x49 0xd7 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p secondTopBytes 31 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 34 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+34#64) 14#5 9#5) from
    add_r64_r64_effect_step (p+34#64) 0x4d 0xce (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p secondTopBytes 34 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 37 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+37#64) 1#5 0#8) from
    adc_r64_imm8_effect_step (p+37#64) 0x48 0xd1 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p secondTopBytes 37 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 41 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (setccR8Effect (p+41#64) 3 2#5 2#4) from
    setcc_r8_effect_step (p+41#64) 0x92 0xc2 (by left; rfl) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p secondTopBytes 41 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 44 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+44#64) 1#5 0#5) from
    add_r64_r64_effect_step (p+44#64) 0x48 0xc1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p secondTopBytes 44 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 47 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+47#64) 15#5 0#8) from
    adc_r64_imm8_effect_step (p+47#64) 0x49 0xd7 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p secondTopBytes 47 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 51 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR8Imm8LegacyEffect (p+51#64) 2#5 255#8) from
    add_r8_imm8_legacy_effect_step (p+51#64) 0xc2 255 (by decide) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p secondTopBytes 51 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 54 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64R64Effect (p+54#64) 15#5 6#5) from
    adc_r64_r64_effect_step (p+54#64) 0x49 0xf7 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p secondTopBytes 54 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 57 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (setccM8Effect (p+57#64) 5 (.sib 4 none 0 (.d8 7)) 2#4) from
    setcc_m8_effect_step (p+57#64) 0x92 (by left; rfl) 0 (.sib 4 none 0 (.d8 7)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p secondTopBytes 57 5)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact scratch_byte_writable hP.memory 7 (by decide)
      · x86_norm
        intro i hi j hj
        have h := hP.codeApart (7+i) (by omega) (57+j) (by omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 7 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 62 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [secondTopEffect, BitVec.add_assoc]
  · x86_norm [secondTopEffect, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
      restore_carry, BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
    all_goals try simp only [eq_self, or_true, true_or]
  · intro i
    cases i <;> x86_norm [secondTopEffect, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
      restore_carry, BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
  · x86_norm [secondTopEffect]

theorem secondTop_bytes :
    Extracted.textBytes.toListFrom 0x147f2 secondTopBytes.length = secondTopBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
