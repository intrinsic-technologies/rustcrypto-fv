import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Common

set_option autoImplicit false

open P256.Proofs.Common.Instructions (imulR64M64Effect imul_r64_m64_effect_step mulHigh64 mulM64Effect mul_m64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64R64Effect adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def fourthStartBytes : List UInt8 :=
  [0x48, 0x89, 0xf0, 0x48, 0xf7, 0x64, 0x24, 0x48, 0x48, 0x89, 0xd1, 0x49, 0x89, 0xc4, 0x4c, 0x8d, 0x3c, 0x18, 0x4c, 0xf, 0xaf, 0x7c, 0x24, 0x50, 0x4c, 0x89, 0xf8, 0x48, 0xf7, 0x64, 0x24, 0x30, 0x48, 0x89, 0xc5, 0x49, 0x89, 0xd0, 0x4c, 0x1, 0xe3, 0x48, 0x11, 0xcd, 0x49, 0x83, 0xd0, 0x0, 0x4c, 0x89, 0xf8, 0x48, 0xf7, 0x64, 0x24, 0x20, 0x49, 0x89, 0xd4, 0x49, 0x89, 0xc5, 0x48, 0x89, 0xf0, 0x48, 0xf7, 0x64, 0x24, 0x10, 0x48, 0x89, 0xc1, 0x48, 0x89, 0x54, 0x24, 0x10, 0x49, 0x1, 0xec, 0x49, 0x83, 0xd0, 0x0, 0x49, 0x1, 0xdd, 0x49, 0x83, 0xd4, 0x0, 0x49, 0x83, 0xd0, 0x0]

def fourthStartEffect (p : BitVec 64) (s : RamState) : Effect :=
  let m1 := (((Operand.reg 6#5 : Operand 64).read s)*(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+72#64) : Operand 64).read s, mulHigh64 ((Operand.reg 6#5 : Operand 64).read s) ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+72#64) : Operand 64).read s))
  let lea4 := m1.1+((Operand.reg 3#5 : Operand 64).read s)
  let m5 := lea4*(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+80#64) : Operand 64).read s
  let m7 := (m5*(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+48#64) : Operand 64).read s, mulHigh64 m5 ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+48#64) : Operand 64).read s))
  let a10 := addSpec (((Operand.reg 3#5 : Operand 64).read s)) (m1.1)
  let c11 := adcSpec m7.1 (m1.2) (BitVec.ofBool a10.2.CF)
  let c12 := adcSpec m7.2 (0#64) (BitVec.ofBool c11.2.CF)
  let m14 := (m5*(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+32#64) : Operand 64).read s, mulHigh64 m5 ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+32#64) : Operand 64).read s))
  let m18 := (((Operand.reg 6#5 : Operand 64).read s)*(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+16#64) : Operand 64).read s, mulHigh64 ((Operand.reg 6#5 : Operand 64).read s) ((Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+16#64) : Operand 64).read s))
  let a21 := addSpec (m14.2) (c11.1)
  let c22 := adcSpec c12.1 (0#64) (BitVec.ofBool a21.2.CF)
  let a23 := addSpec (m14.1) (a10.1)
  let c24 := adcSpec a21.1 (0#64) (BitVec.ofBool a23.2.CF)
  let c25 := adcSpec c22.1 (0#64) (BitVec.ofBool c24.2.CF)
  { rip := p+96#64
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), m18.1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), m18.2⟩,
      ⟨(Operand.reg 1#5 : Operand 64), m18.1⟩,
      ⟨(Operand.reg 12#5 : Operand 64), c24.1⟩,
      ⟨(Operand.reg 15#5 : Operand 64), m5⟩,
      ⟨(Operand.reg 5#5 : Operand 64), c11.1⟩,
      ⟨(Operand.reg 8#5 : Operand 64), c25.1⟩,
      ⟨(Operand.reg 3#5 : Operand 64), a10.1⟩,
      ⟨(Operand.reg 13#5 : Operand 64), a23.1⟩,
      ⟨(Operand.mem (((Operand.reg 4#5 : Operand 64).read s)+16#64) : Operand 64), m18.2⟩]
    flags := some (.ofStatusFlags c25.2) }

theorem fourthStart_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 96 → p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (BlockPre p 96) (codeRange p fourthStartBytes)
      (Effect.post (fourthStartEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect p 0#5 6#5) from
    mov_r64_r64_effect_step p 0x48 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 0 3)
  try (case pre => intro s hP; exact hP.rip)
  case next =>
    intro s hP
    exact next 3 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulM64Effect (p+3#64) (.sib 4 none 0 (.d8 72))) from
    mul_m64_effect_step (p+3#64) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 3 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 72 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 8 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+8#64) 1#5 2#5) from
    mov_r64_r64_effect_step (p+8#64) 0x48 0xd1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 8 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 11 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+11#64) 12#5 0#5) from
    mov_r64_r64_effect_step (p+11#64) 0x49 0xc4 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 11 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 14 (by decide) (by decide)
  advance_then (show StepEffect _ _ (leaR64Effect (p+14#64) 15#5 (.sib 0 (some 3) 0 .none)) from
    lea_r64_effect_step (p+14#64) 0x4c (by simp [RexWPrefix]) 7 (.sib 0 (some 3) 0 .none) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 14 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 18 (by decide) (by decide)
  advance_then (show StepEffect _ _ (imulR64M64Effect (p+18#64) 15#5 (.sib 4 none 0 (.d8 80))) from
    imul_r64_m64_effect_step (p+18#64) 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 18 6)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 80 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 24 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+24#64) 0#5 15#5) from
    mov_r64_r64_effect_step (p+24#64) 0x4c 0xf8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 24 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 27 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulM64Effect (p+27#64) (.sib 4 none 0 (.d8 48))) from
    mul_m64_effect_step (p+27#64) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 27 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 48 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 32 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+32#64) 5#5 0#5) from
    mov_r64_r64_effect_step (p+32#64) 0x48 0xc5 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 32 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 35 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+35#64) 8#5 2#5) from
    mov_r64_r64_effect_step (p+35#64) 0x49 0xd0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 35 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 38 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+38#64) 3#5 12#5) from
    add_r64_r64_effect_step (p+38#64) 0x4c 0xe3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 38 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 41 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64R64Effect (p+41#64) 5#5 1#5) from
    adc_r64_r64_effect_step (p+41#64) 0x48 0xcd (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 41 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 44 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+44#64) 8#5 0#8) from
    adc_r64_imm8_effect_step (p+44#64) 0x49 0xd0 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 44 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 48 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+48#64) 0#5 15#5) from
    mov_r64_r64_effect_step (p+48#64) 0x4c 0xf8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 48 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 51 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulM64Effect (p+51#64) (.sib 4 none 0 (.d8 32))) from
    mul_m64_effect_step (p+51#64) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 51 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 32 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 56 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+56#64) 12#5 2#5) from
    mov_r64_r64_effect_step (p+56#64) 0x49 0xd4 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 56 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 59 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+59#64) 13#5 0#5) from
    mov_r64_r64_effect_step (p+59#64) 0x49 0xc5 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 59 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 62 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+62#64) 0#5 6#5) from
    mov_r64_r64_effect_step (p+62#64) 0x48 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 62 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 65 (by decide) (by decide)
  advance_then (show StepEffect _ _ (mulM64Effect (p+65#64) (.sib 4 none 0 (.d8 16))) from
    mul_m64_effect_step (p+65#64) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 65 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      exact (hP.memory.scratch 16 8 (by decide) (by decide) (by decide)).readable
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 70 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+70#64) 1#5 0#5) from
    mov_r64_r64_effect_step (p+70#64) 0x48 0xc1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 70 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 73 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+73#64) 2#5 (.sib 4 none 0 (.d8 16))) from
    mov_m64_r64_effect_step (p+73#64) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 73 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 16 8 (by decide) (by decide) (by decide)
      · x86_norm
        intro i hi j hj
        have h := hP.codeApart (16+i) (by omega) (73+j) (by omega)
        simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 16 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 78 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+78#64) 12#5 5#5) from
    add_r64_r64_effect_step (p+78#64) 0x49 0xec (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 78 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 81 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+81#64) 8#5 0#8) from
    adc_r64_imm8_effect_step (p+81#64) 0x49 0xd0 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 81 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 85 (by decide) (by decide)
  advance_then (show StepEffect _ _ (addR64R64Effect (p+85#64) 13#5 3#5) from
    add_r64_r64_effect_step (p+85#64) 0x49 0xdd (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 85 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 88 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+88#64) 12#5 0#8) from
    adc_r64_imm8_effect_step (p+88#64) 0x49 0xd4 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 88 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 92 (by decide) (by decide)
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect (p+92#64) 8#5 0#8) from
    adc_r64_imm8_effect_step (p+92#64) 0x49 0xd0 0#8 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset p fourthStartBytes 92 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 96 (by decide) (by decide)
  advance_finish [fourthStartEffect, addSpec_low, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
    restore_carry, BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero]

theorem fourthStart_bytes :
    Extracted.textBytes.toListFrom 0x1492f fourthStartBytes.length = fourthStartBytes := by
  decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
