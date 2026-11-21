import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstProducts
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Carry

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64 mulR64Effect mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcSpec adc_r64_imm8_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def firstCarryBytes : List UInt8 :=
  [0x48, 0x8b, 0x51, 0x8, 0x48, 0x89, 0x54, 0x24, 0x30, 0x4c, 0x89, 0xf0, 0x48, 0xf7, 0xe2, 0x48, 0x89, 0xd5, 0x49, 0x89, 0xc2, 0x49, 0x1, 0xda, 0x48, 0x83, 0xd5, 0x0, 0x4d, 0x1, 0xe2, 0x48, 0x83, 0xd5, 0x0, 0x49, 0x1, 0xf5, 0x49, 0x83, 0xd2, 0x0, 0x48, 0x83, 0xd5, 0x0]

structure FirstCarryPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  memory : Reduction.MemoryPre s
  codeApart : RangeApart ((Operand.reg 4#5 : Operand 64).read s) 112 p firstCarryBytes.length
  modulus : MemReadable s ((Operand.reg 1#5 : Operand 64).read s+8#64) 8

private theorem addSpec_low {n : Nat} (a b : BitVec n) : (addSpec a b).1 = a+b := rfl

def firstCarryEffect (p : BitVec 64) (s : RamState) : Effect :=
  let p1 := (Operand.mem ((Operand.reg 1#5 : Operand 64).read s+8#64) : Operand 64).read s
  let q := (Operand.reg 14#5 : Operand 64).read s
  let x := addSpec (q*p1) ((Operand.reg 3#5 : Operand 64).read s)
  let y := adcSpec (mulHigh64 q p1) 0#64 (BitVec.ofBool x.2.CF)
  let z := addSpec x.1 ((Operand.reg 12#5 : Operand 64).read s)
  let w := adcSpec y.1 0#64 (BitVec.ofBool z.2.CF)
  let k := addSpec ((Operand.reg 13#5 : Operand 64).read s) ((Operand.reg 6#5 : Operand 64).read s)
  let n := adcSpec z.1 0#64 (BitVec.ofBool k.2.CF)
  let o := adcSpec w.1 0#64 (BitVec.ofBool n.2.CF)
  { rip := p+46#64
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), q*p1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), mulHigh64 q p1⟩,
      ⟨(Operand.reg 5#5 : Operand 64), o.1⟩,
      ⟨(Operand.reg 10#5 : Operand 64), n.1⟩,
      ⟨(Operand.reg 13#5 : Operand 64), k.1⟩,
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s+48#64) : Operand 64), p1⟩]
    flags := some (.ofStatusFlags o.2) }

theorem firstCarry_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 46 →
      p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (FirstCarryPre p) (codeRange p firstCarryBytes)
      (Effect.post (firstCarryEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64M64Effect p 2#5 (.base 1 (.d8 8))) from
    mov_r64_m64_effect_step p 0x48 (by simp [RexWPrefix]) 2 (.base 1 (.d8 8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 0 4)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.modulus⟩
  case next =>
    intro s hP
    exact next 4 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+4#64) 2#5 (.sib 4 none 0 (.d8 48))) from
    mov_m64_r64_effect_step (p+4#64) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 4 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 48 8 (by decide) (by decide) (by decide)
      · x86_norm
        intro i hi j hj
        have h := hP.codeApart (48+i) (by omega) (4+j) (by change 4+j < 46; omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 48 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 9 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+9#64) 0#5 14#5) from
    mov_r64_r64_effect_step (p+9#64) 0x4c 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 9 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 12 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulR64Effect (p+12#64) 2#5) from
    mul_r64_effect_step (p+12#64) 0x48 0xe2 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 12 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 15 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+15#64) 5#5 2#5) from
    mov_r64_r64_effect_step (p+15#64) 0x48 0xd5 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 15 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 18 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+18#64) 10#5 0#5) from
    mov_r64_r64_effect_step (p+18#64) 0x49 0xc2 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 18 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 21 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+21#64) 10#5 3#5) from
    add_r64_r64_effect_step (p+21#64) 0x49 0xda (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 21 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 24 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+24#64) 5#5 0#8) from
    adc_r64_imm8_effect_step (p+24#64) 0x48 0xd5 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 24 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 28 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+28#64) 10#5 12#5) from
    add_r64_r64_effect_step (p+28#64) 0x4d 0xe2 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 28 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 31 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+31#64) 5#5 0#8) from
    adc_r64_imm8_effect_step (p+31#64) 0x48 0xd5 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 31 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 35 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+35#64) 13#5 6#5) from
    add_r64_r64_effect_step (p+35#64) 0x49 0xf5 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 35 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 38 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+38#64) 10#5 0#8) from
    adc_r64_imm8_effect_step (p+38#64) 0x49 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 38 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 42 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+42#64) 5#5 0#8) from
    adc_r64_imm8_effect_step (p+42#64) 0x48 0xd5 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p firstCarryBytes 42 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm [BitVec.add_assoc]),
      P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 46 (by decide) (by decide)
  advance_finish [firstCarryEffect, addSpec_low, BitVec.add_assoc, BitVec.add_zero]

theorem firstCarry_bytes :
    Extracted.textBytes.toListFrom 0x14642 firstCarryBytes.length = firstCarryBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery
