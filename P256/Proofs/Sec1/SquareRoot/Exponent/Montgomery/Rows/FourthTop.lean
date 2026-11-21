import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Common

set_option autoImplicit false

open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcSpec adc_r64_imm8_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccM8Effect setcc_m8_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def fourthTopBytes : List UInt8 :=
  [0x44, 0xf, 0xb6, 0x54, 0x24, 0x18, 0x4c, 0x1, 0xf2, 0x49, 0x83, 0xd2, 0x0, 0x4c, 0x1, 0xc8, 0x48, 0x83, 0xd2, 0x0, 0xf, 0x92, 0x44, 0x24, 0x10, 0x4d, 0x89, 0xd7, 0x49, 0x83, 0xd7, 0x0]

def fourthTopEffect (p : BitVec 64) (s : RamState) : Effect :=
  let l0 := ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+24#64) : Operand 8).read s).setWidth 64
  let a1 := addSpec (((Operand.reg 2#5 : Operand 64).read s)) (((Operand.reg 14#5 : Operand 64).read s))
  let c2 := adcSpec l0 (0#64) (BitVec.ofBool a1.2.CF)
  let a3 := addSpec (((Operand.reg 0#5 : Operand 64).read s)) (((Operand.reg 9#5 : Operand 64).read s))
  let c4 := adcSpec (((Operand.reg 2#5 : Operand 64).read s)+((Operand.reg 14#5 : Operand 64).read s)) (0#64) (BitVec.ofBool a3.2.CF)
  let c7 := adcSpec c2.1 (0#64) (BitVec.ofBool c4.2.CF)
  { rip := p+32#64
    writes := [
      ⟨(Operand.reg 10#5 : Operand 64), c2.1⟩,
      ⟨(Operand.reg 0#5 : Operand 64), (((Operand.reg 0#5 : Operand 64).read s)+((Operand.reg 9#5 : Operand 64).read s))⟩,
      ⟨(Operand.reg 2#5 : Operand 64), c4.1⟩,
      ⟨(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+16#64) : Operand 8), (if c4.2.CF then 1#8 else 0#8)⟩,
      ⟨(Operand.reg 15#5 : Operand 64), c7.1⟩]
    flags := some (.ofStatusFlags c7.2) }

theorem fourthTop_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 32 → p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (BlockPre p 32) (codeRange p fourthTopBytes)
      (Effect.post (fourthTopEffect p)) := by
  advance_begin (show StepEffect _ _ (movzxR32M8Effect p 6 10#5 (.sib 4 none 0 (.d8 24))) from
    movzx_r_m8_rex_effect_step p 0x44 (by simp [RexPrefix]) 32 (by right; rfl) (by intro seg; rfl) 2 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p fourthTopBytes 0 6)
  try (case pre => intro s hP; exact hP.rip)
  case pre =>
    intro s hP
    exact ⟨hP.rip, (scratch_byte_writable hP.memory 24 (by decide)).readable⟩
  case next =>
    intro s hP
    exact next 6 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+6#64) 2#5 14#5) from
    add_r64_r64_effect_step (p+6#64) 0x4c 0xf2 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthTopBytes 6 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 9 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+9#64) 10#5 0#8) from
    adc_r64_imm8_effect_step (p+9#64) 0x49 0xd2 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthTopBytes 9 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 13 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+13#64) 0#5 9#5) from
    add_r64_r64_effect_step (p+13#64) 0x4c 0xc8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthTopBytes 13 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 16 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+16#64) 2#5 0#8) from
    adc_r64_imm8_effect_step (p+16#64) 0x48 0xd2 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthTopBytes 16 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 20 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (setccM8Effect (p+20#64) 5 (.sib 4 none 0 (.d8 16)) 2#4) from
    setcc_m8_effect_step (p+20#64) 0x92 (by left; rfl) 0 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p fourthTopBytes 20 5)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact scratch_byte_writable hP.memory 16 (by decide)
      · x86_norm
        intro i hi j hj
        have h := hP.codeApart (16+i) (by omega) (20+j) (by omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 16 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 25 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+25#64) 15#5 10#5) from
    mov_r64_r64_effect_step (p+25#64) 0x4d 0xd7 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthTopBytes 25 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 28 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+28#64) 15#5 0#8) from
    adc_r64_imm8_effect_step (p+28#64) 0x49 0xd7 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthTopBytes 28 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 32 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [fourthTopEffect, BitVec.add_assoc]
  · x86_norm [fourthTopEffect, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
      restore_carry, BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
    all_goals try simp only [eq_self, or_true, true_or]
  · intro i
    cases i <;> x86_norm [fourthTopEffect, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
      restore_carry, BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]
  · x86_norm [fourthTopEffect]

theorem fourthTop_bytes :
    Extracted.textBytes.toListFrom 0x149f0 fourthTopBytes.length = fourthTopBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
