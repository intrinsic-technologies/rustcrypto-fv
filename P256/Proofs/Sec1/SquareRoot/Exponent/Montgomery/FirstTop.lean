import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstHigh
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.ByteMemory
import P256.Proofs.Common.Instructions.AddByte.Legacy
import P256.Proofs.Common.EffectCompose.Conditions
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64 mulR64Effect mul_r64_effect_step)
open P256.Proofs.Common.Instructions.AddByte (addR8Imm8LegacyEffect add_cl_ff_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64R64Effect adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccM8Effect setccR8Effect setcc_m8_effect_step setcc_r8_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def firstTopBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x18, 0x4c, 0x8b, 0x70, 0x8, 0x4c, 0x89, 0xf0, 0x49, 0xf7, 0xe3, 0x4d, 0x1, 0xc7, 0x49, 0x11, 0xc9, 0xf, 0x92, 0xc1, 0x49, 0x1, 0xc1, 0x48, 0x83, 0xd2, 0x0, 0x80, 0xc1, 0xff, 0x48, 0x83, 0xd2, 0x0, 0x48, 0x89, 0x54, 0x24, 0x68, 0xf, 0x92, 0x44, 0x24, 0x7]

structure FirstTopPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  memory : Reduction.MemoryPre s
  codeApart : RangeApart ((Operand.reg 4#5 : Operand 64).read s) 112 p firstTopBytes.length
  input : MemReadable s
    ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s+24#64) : Operand 64).read s+8#64) 8

private theorem addSpec_low {n : Nat} (a b : BitVec n) : (addSpec a b).1 = a+b := rfl

private theorem restore_carry (c : Bool) :
    (addSpec (if c then 1#8 else 0#8) 255#8).2.CF = c := by
  cases c <;> decide +kernel

def firstTopEffect (p : BitVec 64) (s : RamState) : Effect :=
  let ptr := (Operand.mem ((Operand.reg 4#5 : Operand 64).read s+24#64) : Operand 64).read s
  let next := (Operand.mem (ptr+8#64) : Operand 64).read s
  let b := (Operand.reg 11#5 : Operand 64).read s
  let l := addSpec ((Operand.reg 15#5 : Operand 64).read s) ((Operand.reg 8#5 : Operand 64).read s)
  let m := adcSpec ((Operand.reg 9#5 : Operand 64).read s) ((Operand.reg 1#5 : Operand 64).read s)
    (BitVec.ofBool l.2.CF)
  let n := addSpec m.1 (next*b)
  let h := adcSpec (mulHigh64 next b) 0#64 (BitVec.ofBool n.2.CF)
  let k := adcSpec h.1 0#64 (BitVec.ofBool m.2.CF)
  let save := mergeGPR 8 (if m.2.CF then 1#8 else 0#8) ((Operand.reg 1#5 : Operand 64).read s)
  { rip := p+48#64
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), next*b⟩,
      ⟨(Operand.reg 14#5 : Operand 64), next⟩,
      ⟨(Operand.reg 2#5 : Operand 64), k.1⟩,
      ⟨(Operand.reg 15#5 : Operand 64), l.1⟩,
      ⟨(Operand.reg 9#5 : Operand 64), n.1⟩,
      ⟨(Operand.reg 1#5 : Operand 64), mergeGPR 8 ((if m.2.CF then 1#8 else 0#8)+255#8) save⟩,
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s+104#64) : Operand 64), k.1⟩,
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s+7#64) : Operand 8), if k.2.CF then 1#8 else 0#8⟩]
    flags := some (.ofStatusFlags k.2) }

theorem firstTop_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 48 →
      p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (FirstTopPre p) (codeRange p firstTopBytes)
      (Effect.post (firstTopEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64M64Effect p 0#5 (.sib 4 none 0 (.d8 24))) from
    mov_r64_m64_effect_step p 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstTopBytes 0 5)
  case pre =>
    intro s hP
    exact ⟨hP.rip, (hP.memory.scratch 24 8 (by decide) (by decide) (by decide)).readable⟩
  case next =>
    intro s hP
    exact next 5 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+5#64) 14#5 (.base 0 (.d8 8))) from
    mov_r64_m64_effect_step (p+5#64) 0x4c (by simp [RexWPrefix]) 6 (.base 0 (.d8 8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstTopBytes 5 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact hP.input
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 9 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+9#64) 0#5 14#5) from
    mov_r64_r64_effect_step (p+9#64) 0x4c 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstTopBytes 9 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 12 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulR64Effect (p+12#64) 11#5) from
    mul_r64_effect_step (p+12#64) 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstTopBytes 12 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 15 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+15#64) 15#5 8#5) from
    add_r64_r64_effect_step (p+15#64) 0x4d 0xc7 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstTopBytes 15 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 18 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64R64Effect (p+18#64) 9#5 1#5) from
    adc_r64_r64_effect_step (p+18#64) 0x49 0xc9 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstTopBytes 18 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 21 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (setccR8Effect (p+21#64) 3 1#5 2#4) from
    setcc_r8_effect_step (p+21#64) 0x92 0xc1 (by left; rfl) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstTopBytes 21 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 24 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+24#64) 9#5 0#5) from
    add_r64_r64_effect_step (p+24#64) 0x49 0xc1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstTopBytes 24 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 27 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+27#64) 2#5 0#8) from
    adc_r64_imm8_effect_step (p+27#64) 0x48 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstTopBytes 27 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 31 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR8Imm8LegacyEffect (p+31#64) 1#5 255#8) from
    add_cl_ff_effect_step (p+31#64))
  try (case sub => exact codeRange_slice_subset p firstTopBytes 31 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 34 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+34#64) 2#5 0#8) from
    adc_r64_imm8_effect_step (p+34#64) 0x48 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstTopBytes 34 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 38 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+38#64) 2#5 (.sib 4 none 0 (.d8 104))) from
    mov_m64_r64_effect_step (p+38#64) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstTopBytes 38 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 104 8 (by decide) (by decide) (by decide)
      · x86_norm
        intro i hi j hj
        have h := hP.codeApart (104+i) (by omega) (38+j) (by change 38+j < 48; omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 104 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 43 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (setccM8Effect (p+43#64) 5 (.sib 4 none 0 (.d8 7)) 2#4) from
    setcc_m8_effect_step (p+43#64) 0x92 (by left; rfl) 0 (.sib 4 none 0 (.d8 7)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstTopBytes 43 5)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact scratch_byte_writable hP.memory 7 (by decide)
      · x86_norm
        intro i hi j hj
        have h := hP.codeApart (7+i) (by omega) (43+j) (by change 43+j < 48; omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 7 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 48 (by decide) (by decide)
  advance_finish [firstTopEffect, addSpec_low, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
    restore_carry, BitVec.add_assoc]

theorem firstTop_bytes :
    Extracted.textBytes.toListFrom 0x146f9 firstTopBytes.length = firstTopBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery
