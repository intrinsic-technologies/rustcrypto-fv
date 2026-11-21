import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Field.Schoolbook.Frame
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Instructions (add_r64_m64_effect_step mulHigh64 mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.AddByte (addR8Imm8Effect add_r8_imm8_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect_components adcR64M64Effect_components adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_m64_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setcc_r8_rex_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Common.Field
open P256.Proofs.Common.Field.Montgomery.Schoolbook
open P256.Spec.Program.Routines

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem lowerSums_addSpec_fst {n : Nat} (a b : BitVec n) : (addSpec a b).1 = a+b := rfl

attribute [local x86_compose] lowerSums_addSpec_fst

def lowerSumsFirstBytes : List UInt8 :=
  [0x4d, 0x1, 0xe0, 0x4d, 0x11, 0xef, 0x48, 0x11, 0xe9, 0x40, 0xf, 0x92, 0xc5]

def lowerSumsFirstEffect (s : RamState) : Effect :=
  let v0 := addSpec ((Operand.reg 8 : Operand 64).read s) ((Operand.reg 12 : Operand 64).read s)
  let v1 := adcSpec ((Operand.reg 15 : Operand 64).read s) ((Operand.reg 13 : Operand 64).read s) (BitVec.ofBool v0.2.CF)
  let v2 := adcSpec ((Operand.reg 1 : Operand 64).read s) ((Operand.reg 5 : Operand 64).read s) (BitVec.ofBool v1.2.CF)
  { rip := 0x11ca03
    writes := [
      ⟨(Operand.reg 1 : Operand 64), v2.1⟩,
      ⟨(Operand.reg 5 : Operand 64), (mergeGPR 8 (if v2.2.CF then 1#8 else 0#8) ((Operand.reg 5 : Operand 64).read s))⟩,
      ⟨(Operand.reg 8 : Operand 64), v0.1⟩,
      ⟨(Operand.reg 15 : Operand 64), v1.1⟩]
    flags := some (.ofStatusFlags v2.2) }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem lower_sums_first [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (ScratchPre 0x11c9f6 13)
      (codeRange 0x11c9f6 lowerSumsFirstBytes) (Effect.post lowerSumsFirstEffect) := by
  advance_begin (add_r64_r64_effect_step 0x11c9f6 0x4d 0xe0
    (by simp [RexWPrefix]) (by decide))
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9f9 (by decide))
  refine AdvanceTriple.block_then_on ?k1 (adc_r64_r64_effect_step 0x11c9f9 0x4d 0xef
    (by simp [RexWPrefix]) (by decide)) [.CF] ?loc1 ?sub1 ?full1 ?known1 ?mid1
  case loc1 => simp (config := { decide := true }) only [x86_local_on]
  case sub1 => exact codeRange_slice_subset 0x11c9f6 lowerSumsFirstBytes 3 3
  case full1 => x86_full
  case known1 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid1 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [adcR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9fc (by decide))
  case' k1 => x86_norm
  refine AdvanceTriple.block_then_on ?k2 (adc_r64_r64_effect_step 0x11c9fc 0x48 0xe9
    (by simp [RexWPrefix]) (by decide)) [.CF] ?loc2 ?sub2 ?full2 ?known2 ?mid2
  case loc2 => simp (config := { decide := true }) only [x86_local_on]
  case sub2 => exact codeRange_slice_subset 0x11c9f6 lowerSumsFirstBytes 6 3
  case full2 => x86_full
  case known2 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid2 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [adcR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9ff (by decide))
  case' k2 => x86_norm
  refine AdvanceTriple.block_then_on ?k3 (setcc_r8_rex_effect_step 0x11c9ff 0x40 0x92 0xc5
    (by simp [RexPrefix]) (.inl rfl) (by decide)) [.CF] ?loc3 ?sub3 ?full3 ?known3 ?mid3
  case loc3 => simp (config := { decide := true }) only [x86_local_on]
  case sub3 => exact codeRange_slice_subset 0x11c9f6 lowerSumsFirstBytes 9 4
  case full3 => x86_full
  case known3 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid3 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [setccR8Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca03 (by decide))
  case' k3 => x86_norm
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [lowerSumsFirstEffect]
  · x86_norm [lowerSumsFirstEffect, BitVec.add_zero]
    all_goals (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · intro i; cases i <;> x86_norm [lowerSumsFirstEffect, BitVec.add_zero]
    all_goals (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · x86_norm [lowerSumsFirstEffect, BitVec.add_zero]

def lowerSumsSecondBytes : List UInt8 :=
  [0x4c, 0x3, 0x44, 0x24, 0x18, 0x4c, 0x89, 0x44, 0x24, 0x18, 0x48, 0x13, 0x34, 0x24, 0x49, 0x83, 0xd3, 0x0, 0x4c, 0x1, 0xfe, 0x48, 0x89, 0x34, 0x24, 0x49, 0x83, 0xd3, 0x0]

def lowerSumsSecondEffect (s : RamState) : Effect :=
  let v0 := addSpec ((Operand.reg 8 : Operand 64).read s) ((Operand.mem (rspOf s+24#64) : Operand 64).read s)
  let v2 := adcSpec ((Operand.reg 6 : Operand 64).read s) ((Operand.mem (rspOf s) : Operand 64).read s) (BitVec.ofBool v0.2.CF)
  let v3 := adcSpec ((Operand.reg 11 : Operand 64).read s) 0#64 (BitVec.ofBool v2.2.CF)
  let v4 := addSpec v2.1 ((Operand.reg 15 : Operand 64).read s)
  let v6 := adcSpec v3.1 0#64 (BitVec.ofBool v4.2.CF)
  { rip := 0x11ca20
    writes := [
      ⟨(Operand.reg 6 : Operand 64), v4.1⟩,
      ⟨(Operand.reg 8 : Operand 64), v0.1⟩,
      ⟨(Operand.reg 11 : Operand 64), v6.1⟩,
      ⟨(Operand.mem (rspOf s) : Operand 64), v4.1⟩,
      ⟨(Operand.mem (rspOf s+24#64) : Operand 64), v0.1⟩]
    flags := some (.ofStatusFlags v6.2) }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem lower_sums_second [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (ScratchPre 0x11ca03 29)
      (codeRange 0x11ca03 lowerSumsSecondBytes) (Effect.post lowerSumsSecondEffect) := by
  advance_begin (add_r64_m64_effect_step 0x11ca03 0x4c
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    schoolbook_frame
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca08 (by decide))
  refine AdvanceTriple.block_then ?k4 (mov_m64_r64_effect_step 0x11ca08 0x4c
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl) ?loc4 ?sub4 ?full4 ?mid4
  case loc4 => x86_local
  case sub4 => exact codeRange_slice_subset 0x11ca03 lowerSumsSecondBytes 5 5
  case full4 => x86_full
  case mid4 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        schoolbook_frame
      · x86_norm
        exact hP.apart 24 (by decide) 5 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca0d (by decide))
  case' k4 => x86_norm
  refine AdvanceTriple.block_then_on ?k5 (adc_r64_m64_effect_step 0x11ca0d 0x48
    (by simp [RexWPrefix]) 6 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl) [.CF] ?loc5 ?sub5 ?full5 ?known5 ?mid5
  case loc5 => simp (config := { decide := true }) only [x86_local_on]
  case sub5 => exact codeRange_slice_subset 0x11ca03 lowerSumsSecondBytes 10 4
  case full5 => x86_full
  case known5 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid5 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      schoolbook_frame
    · apply Effect.Avoids.of_noMem
      simp [adcR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca11 (by decide))
  case' k5 => x86_norm
  refine AdvanceTriple.block_then_on ?k6 (adc_r64_imm8_effect_step 0x11ca11 0x49 0xd3 0
    (by simp [RexWPrefix]) (by decide) (by decide)) [.CF] ?loc6 ?sub6 ?full6 ?known6 ?mid6
  case loc6 => simp (config := { decide := true }) only [x86_local_on]
  case sub6 => exact codeRange_slice_subset 0x11ca03 lowerSumsSecondBytes 14 4
  case full6 => x86_full
  case known6 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid6 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca15 (by decide))
  case' k6 => x86_norm
  refine AdvanceTriple.block_then ?k7 (add_r64_r64_effect_step 0x11ca15 0x4c 0xfe
    (by simp [RexWPrefix]) (by decide)) ?loc7 ?sub7 ?full7 ?mid7
  case loc7 => x86_local
  case sub7 => exact codeRange_slice_subset 0x11ca03 lowerSumsSecondBytes 18 3
  case full7 => x86_full
  case mid7 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [addR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca18 (by decide))
  case' k7 => x86_norm
  refine AdvanceTriple.block_then ?k8 (mov_m64_r64_effect_step 0x11ca18 0x48
    (by simp [RexWPrefix]) 6 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl) ?loc8 ?sub8 ?full8 ?mid8
  case loc8 => x86_local
  case sub8 => exact codeRange_slice_subset 0x11ca03 lowerSumsSecondBytes 21 4
  case full8 => x86_full
  case mid8 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        schoolbook_frame
      · x86_norm
        exact hP.apart 0 (by decide) 21 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca1c (by decide))
  case' k8 => x86_norm
  refine AdvanceTriple.block_then_on ?k9 (adc_r64_imm8_effect_step 0x11ca1c 0x49 0xd3 0
    (by simp [RexWPrefix]) (by decide) (by decide)) [.CF] ?loc9 ?sub9 ?full9 ?known9 ?mid9
  case loc9 => simp (config := { decide := true }) only [x86_local_on]
  case sub9 => exact codeRange_slice_subset 0x11ca03 lowerSumsSecondBytes 25 4
  case full9 => x86_full
  case known9 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid9 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca20 (by decide))
  case' k9 => x86_norm
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [lowerSumsSecondEffect]
  · x86_norm [lowerSumsSecondEffect, BitVec.add_zero]
    all_goals (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · intro i; cases i <;> x86_norm [lowerSumsSecondEffect, BitVec.add_zero]
    all_goals (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · x86_norm [lowerSumsSecondEffect, BitVec.add_zero]

def lowerSumsThirdBytes : List UInt8 :=
  [0x4d, 0x89, 0xce, 0x4c, 0x89, 0x4c, 0x24, 0x28, 0x4c, 0x89, 0xc8, 0x49, 0xf7, 0xe2, 0x49, 0x89, 0xd1, 0x49, 0x89, 0xc0, 0x4d, 0x1, 0xd8, 0x49, 0x83, 0xd1, 0x0, 0x49, 0x1, 0xc8, 0x49, 0x83, 0xd1, 0x0]

def lowerSumsThirdEffect (s : RamState) : Effect :=
  let p3 := ((Operand.reg 9 : Operand 64).read s) * ((Operand.reg 10 : Operand 64).read s)
  let h3 := mulHigh64 ((Operand.reg 9 : Operand 64).read s) ((Operand.reg 10 : Operand 64).read s)
  let v6 := addSpec p3 ((Operand.reg 11 : Operand 64).read s)
  let v7 := adcSpec h3 0#64 (BitVec.ofBool v6.2.CF)
  let v8 := addSpec v6.1 ((Operand.reg 1 : Operand 64).read s)
  let v9 := adcSpec v7.1 0#64 (BitVec.ofBool v8.2.CF)
  { rip := 0x11ca42
    writes := [
      ⟨(Operand.reg 0 : Operand 64), p3⟩,
      ⟨(Operand.reg 2 : Operand 64), h3⟩,
      ⟨(Operand.reg 8 : Operand 64), v8.1⟩,
      ⟨(Operand.reg 9 : Operand 64), v9.1⟩,
      ⟨(Operand.reg 14 : Operand 64), ((Operand.reg 9 : Operand 64).read s)⟩,
      ⟨(Operand.mem (rspOf s+40#64) : Operand 64), ((Operand.reg 9 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags v9.2) }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem lower_sums_third [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (ScratchPre 0x11ca20 34)
      (codeRange 0x11ca20 lowerSumsThirdBytes) (Effect.post lowerSumsThirdEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x11ca20 0x4d 0xce
    (by simp [RexWPrefix]) (by decide))
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca23 (by decide))
  refine AdvanceTriple.block_then ?k10 (mov_m64_r64_effect_step 0x11ca23 0x4c
    (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl) ?loc10 ?sub10 ?full10 ?mid10
  case loc10 => x86_local
  case sub10 => exact codeRange_slice_subset 0x11ca20 lowerSumsThirdBytes 3 5
  case full10 => x86_full
  case mid10 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        schoolbook_frame
      · x86_norm
        exact hP.apart 40 (by decide) 3 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca28 (by decide))
  case' k10 => x86_norm
  refine AdvanceTriple.block_then ?k11 (mov_r64_r64_effect_step 0x11ca28 0x4c 0xc8
    (by simp [RexWPrefix]) (by decide)) ?loc11 ?sub11 ?full11 ?mid11
  case loc11 => x86_local
  case sub11 => exact codeRange_slice_subset 0x11ca20 lowerSumsThirdBytes 8 3
  case full11 => x86_full
  case mid11 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [movR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca2b (by decide))
  case' k11 => x86_norm
  refine AdvanceTriple.block_then ?k12 (mul_r64_effect_step 0x11ca2b 0x49 0xe2
    (by simp [RexWPrefix]) (by decide) (by decide)) ?loc12 ?sub12 ?full12 ?mid12
  case loc12 => x86_local
  case sub12 => exact codeRange_slice_subset 0x11ca20 lowerSumsThirdBytes 11 3
  case full12 => x86_full
  case mid12 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca2e (by decide))
  case' k12 => x86_norm
  refine AdvanceTriple.block_then ?k13 (mov_r64_r64_effect_step 0x11ca2e 0x49 0xd1
    (by simp [RexWPrefix]) (by decide)) ?loc13 ?sub13 ?full13 ?mid13
  case loc13 => x86_local
  case sub13 => exact codeRange_slice_subset 0x11ca20 lowerSumsThirdBytes 14 3
  case full13 => x86_full
  case mid13 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [movR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca31 (by decide))
  case' k13 => x86_norm
  refine AdvanceTriple.block_then ?k14 (mov_r64_r64_effect_step 0x11ca31 0x49 0xc0
    (by simp [RexWPrefix]) (by decide)) ?loc14 ?sub14 ?full14 ?mid14
  case loc14 => x86_local
  case sub14 => exact codeRange_slice_subset 0x11ca20 lowerSumsThirdBytes 17 3
  case full14 => x86_full
  case mid14 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [movR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca34 (by decide))
  case' k14 => x86_norm
  refine AdvanceTriple.block_then ?k15 (add_r64_r64_effect_step 0x11ca34 0x4d 0xd8
    (by simp [RexWPrefix]) (by decide)) ?loc15 ?sub15 ?full15 ?mid15
  case loc15 => x86_local
  case sub15 => exact codeRange_slice_subset 0x11ca20 lowerSumsThirdBytes 20 3
  case full15 => x86_full
  case mid15 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [addR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca37 (by decide))
  case' k15 => x86_norm
  refine AdvanceTriple.block_then_on ?k16 (adc_r64_imm8_effect_step 0x11ca37 0x49 0xd1 0
    (by simp [RexWPrefix]) (by decide) (by decide)) [.CF] ?loc16 ?sub16 ?full16 ?known16 ?mid16
  case loc16 => simp (config := { decide := true }) only [x86_local_on]
  case sub16 => exact codeRange_slice_subset 0x11ca20 lowerSumsThirdBytes 23 4
  case full16 => x86_full
  case known16 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid16 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca3b (by decide))
  case' k16 => x86_norm
  refine AdvanceTriple.block_then ?k17 (add_r64_r64_effect_step 0x11ca3b 0x49 0xc8
    (by simp [RexWPrefix]) (by decide)) ?loc17 ?sub17 ?full17 ?mid17
  case loc17 => x86_local
  case sub17 => exact codeRange_slice_subset 0x11ca20 lowerSumsThirdBytes 27 3
  case full17 => x86_full
  case mid17 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [addR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca3e (by decide))
  case' k17 => x86_norm
  refine AdvanceTriple.block_then_on ?k18 (adc_r64_imm8_effect_step 0x11ca3e 0x49 0xd1 0
    (by simp [RexWPrefix]) (by decide) (by decide)) [.CF] ?loc18 ?sub18 ?full18 ?known18 ?mid18
  case loc18 => simp (config := { decide := true }) only [x86_local_on]
  case sub18 => exact codeRange_slice_subset 0x11ca20 lowerSumsThirdBytes 30 4
  case full18 => x86_full
  case known18 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid18 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca42 (by decide))
  case' k18 => x86_norm
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [lowerSumsThirdEffect]
  · x86_norm [lowerSumsThirdEffect, BitVec.add_zero]
    all_goals (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · intro i; cases i <;> x86_norm [lowerSumsThirdEffect, BitVec.add_zero]
    all_goals (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · x86_norm [lowerSumsThirdEffect, BitVec.add_zero]

def lowerSumsFourthBytes : List UInt8 :=
  [0x48, 0x89, 0x5c, 0x24, 0x38, 0x48, 0x89, 0xd8, 0x49, 0xf7, 0xe2, 0x49, 0x89, 0xd4, 0x49, 0x89, 0xc3, 0x4d, 0x1, 0xcb, 0x49, 0x83, 0xd4, 0x0, 0x40, 0x80, 0xc5, 0xff, 0x4c, 0x13, 0x5c, 0x24, 0x10, 0x48, 0x8b, 0x74, 0x24, 0x8, 0x48, 0x8b, 0x4e, 0x18, 0x49, 0x83, 0xd4, 0x0]

def savedSource (s : RamState) : BitVec 64 :=
  (Operand.mem (rspOf s + 8#64) : Operand 64).read s

structure LowerSumsPre (p : BitVec 64) (codeLen : Nat) (s : RamState) : Prop
    extends ScratchPre p codeLen s where
  left : MemReadable s (savedSource s + 24#64) 8
  apart : RangeApart (rspOf s) 88 (savedSource s + 24#64) 8

theorem lowerSums_load_store {a b : BitVec 64} (apart : RangeApart a 88 b 8)
    (mem : Ram) (c v : BitVec 64) (hc : c.toNat + 8 ≤ 88) :
    memLoad (memStore mem (a+c) v) b 64 = memLoad mem b 64 := by
  apply memLoad_memStore_rangeApart
  intro i hi j hj
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc] using
    apart (c.toNat+i) (by omega) j hj

def lowerSumsFourthEffect (s : RamState) : Effect :=
  let p2 := ((Operand.reg 3 : Operand 64).read s) * ((Operand.reg 10 : Operand 64).read s)
  let h2 := mulHigh64 ((Operand.reg 3 : Operand 64).read s) ((Operand.reg 10 : Operand 64).read s)
  let v5 := addSpec p2 ((Operand.reg 9 : Operand 64).read s)
  let v6 := adcSpec h2 0#64 (BitVec.ofBool v5.2.CF)
  let v7 := addSpec ((Operand.reg 5 : Operand 8).read s) 0xff#8
  let v8 := adcSpec v5.1 ((Operand.mem (rspOf s+16#64) : Operand 64).read s) (BitVec.ofBool v7.2.CF)
  let v11 := adcSpec v6.1 0#64 (BitVec.ofBool v8.2.CF)
  { rip := 0x11ca70
    writes := [
      ⟨(Operand.reg 0 : Operand 64), p2⟩,
      ⟨(Operand.reg 1 : Operand 64), ((Operand.mem (savedSource s + 24#64) : Operand 64).read s)⟩,
      ⟨(Operand.reg 2 : Operand 64), h2⟩,
      ⟨(Operand.reg 5 : Operand 64), (mergeGPR 8 v7.1 ((Operand.reg 5 : Operand 64).read s))⟩,
      ⟨(Operand.reg 6 : Operand 64), ((Operand.mem (rspOf s+8#64) : Operand 64).read s)⟩,
      ⟨(Operand.reg 11 : Operand 64), v8.1⟩,
      ⟨(Operand.reg 12 : Operand 64), v11.1⟩,
      ⟨(Operand.mem (rspOf s+56#64) : Operand 64), ((Operand.reg 3 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags v11.2) }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem lower_sums_fourth [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (LowerSumsPre 0x11ca42 46)
      (codeRange 0x11ca42 lowerSumsFourthBytes) (Effect.post lowerSumsFourthEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x11ca42 0x48
    (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    have hf := hP.toScratchPre
    refine ⟨hP.rip, ?_, ?_⟩
    · x86_norm
      schoolbook_frame
    · x86_norm
      schoolbook_frame
  case av =>
    intro s hP
    have hf := hP.toScratchPre
    schoolbook_avoid
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca47 (by decide))
  refine AdvanceTriple.block_then ?k19 (mov_r64_r64_effect_step 0x11ca47 0x48 0xd8
    (by simp [RexWPrefix]) (by decide)) ?loc19 ?sub19 ?full19 ?mid19
  case loc19 => x86_local
  case sub19 => exact codeRange_slice_subset 0x11ca42 lowerSumsFourthBytes 5 3
  case full19 => x86_full
  case mid19 =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [movR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca4a (by decide))
  case' k19 => x86_norm
  refine AdvanceTriple.block_then ?k20 (mul_r64_effect_step 0x11ca4a 0x49 0xe2
    (by simp [RexWPrefix]) (by decide) (by decide)) ?loc20 ?sub20 ?full20 ?mid20
  case loc20 => x86_local
  case sub20 => exact codeRange_slice_subset 0x11ca42 lowerSumsFourthBytes 8 3
  case full20 => x86_full
  case mid20 =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca4d (by decide))
  case' k20 => x86_norm
  refine AdvanceTriple.block_then ?k21 (mov_r64_r64_effect_step 0x11ca4d 0x49 0xd4
    (by simp [RexWPrefix]) (by decide)) ?loc21 ?sub21 ?full21 ?mid21
  case loc21 => x86_local
  case sub21 => exact codeRange_slice_subset 0x11ca42 lowerSumsFourthBytes 11 3
  case full21 => x86_full
  case mid21 =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [movR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca50 (by decide))
  case' k21 => x86_norm
  refine AdvanceTriple.block_then ?k22 (mov_r64_r64_effect_step 0x11ca50 0x49 0xc3
    (by simp [RexWPrefix]) (by decide)) ?loc22 ?sub22 ?full22 ?mid22
  case loc22 => x86_local
  case sub22 => exact codeRange_slice_subset 0x11ca42 lowerSumsFourthBytes 14 3
  case full22 => x86_full
  case mid22 =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [movR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca53 (by decide))
  case' k22 => x86_norm
  refine AdvanceTriple.block_then ?k23 (add_r64_r64_effect_step 0x11ca53 0x4d 0xcb
    (by simp [RexWPrefix]) (by decide)) ?loc23 ?sub23 ?full23 ?mid23
  case loc23 => x86_local
  case sub23 => exact codeRange_slice_subset 0x11ca42 lowerSumsFourthBytes 17 3
  case full23 => x86_full
  case mid23 =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [addR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca56 (by decide))
  case' k23 => x86_norm
  refine AdvanceTriple.block_then_on ?k24 (adc_r64_imm8_effect_step 0x11ca56 0x49 0xd4 0
    (by simp [RexWPrefix]) (by decide) (by decide)) [.CF] ?loc24 ?sub24 ?full24 ?known24 ?mid24
  case loc24 => simp (config := { decide := true }) only [x86_local_on]
  case sub24 => exact codeRange_slice_subset 0x11ca42 lowerSumsFourthBytes 20 4
  case full24 => x86_full
  case known24 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid24 =>
    intro s t hP hH hO hF
    have hf := hP.toScratchPre
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca5a (by decide))
  case' k24 => x86_norm
  refine AdvanceTriple.block_then ?k25 (add_r8_imm8_effect_step 0x11ca5a 0x40 0xc5 0xff
    (by simp [RexPrefix]) (by decide) (by decide)) ?loc25 ?sub25 ?full25 ?mid25
  case loc25 => x86_local
  case sub25 => exact codeRange_slice_subset 0x11ca42 lowerSumsFourthBytes 24 4
  case full25 => x86_full
  case mid25 =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [addR8Imm8Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca5e (by decide))
  case' k25 => x86_norm
  refine AdvanceTriple.block_then_on ?k26 (adc_r64_m64_effect_step 0x11ca5e 0x4c
    (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl) [.CF] ?loc26 ?sub26 ?full26 ?known26 ?mid26
  case loc26 => simp (config := { decide := true }) only [x86_local_on]
  case sub26 => exact codeRange_slice_subset 0x11ca42 lowerSumsFourthBytes 28 5
  case full26 => x86_full
  case known26 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid26 =>
    intro s t hP hH hO hF
    have hf := hP.toScratchPre
    refine ⟨?_, ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      schoolbook_frame
    · apply Effect.Avoids.of_noMem
      simp [adcR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca63 (by decide))
  case' k26 => x86_norm
  refine AdvanceTriple.block_then ?k27 (mov_r64_m64_effect_step 0x11ca63 0x48
    (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl) ?loc27 ?sub27 ?full27 ?mid27
  case loc27 => x86_local
  case sub27 => exact codeRange_slice_subset 0x11ca42 lowerSumsFourthBytes 33 5
  case full27 => x86_full
  case mid27 =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      schoolbook_frame
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca68 (by decide))
  case' k27 => x86_norm
  refine AdvanceTriple.block_then ?k28 (mov_r64_m64_effect_step 0x11ca68 0x48
    (by simp [RexWPrefix]) 1 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl) ?loc28 ?sub28 ?full28 ?mid28
  case loc28 => x86_local
  case sub28 => exact codeRange_slice_subset 0x11ca42 lowerSumsFourthBytes 38 4
  case full28 => x86_full
  case mid28 =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      exact hP.left
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca6c (by decide))
  case' k28 => x86_norm
  refine AdvanceTriple.block_then_on ?k29 (adc_r64_imm8_effect_step 0x11ca6c 0x49 0xd4 0
    (by simp [RexWPrefix]) (by decide) (by decide)) [.CF] ?loc29 ?sub29 ?full29 ?known29 ?mid29
  case loc29 => simp (config := { decide := true }) only [x86_local_on]
  case sub29 => exact codeRange_slice_subset 0x11ca42 lowerSumsFourthBytes 42 4
  case full29 => x86_full
  case known29 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid29 =>
    intro s t hP hH hO hF
    have hf := hP.toScratchPre
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca70 (by decide))
  case' k29 => x86_norm
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hap := hP.apart
  x86_norm [savedSource] at hap
  apply hH.weaken
  · x86_norm [lowerSumsFourthEffect]
  · simp (config := { decide := true }) (disch := decide +kernel) only
      [x86_compose, lowerSumsFourthEffect, savedSource, lowerSums_load_store hap]
    all_goals (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · intro i; cases i <;> x86_norm [lowerSumsFourthEffect, BitVec.add_zero]
    all_goals (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · x86_norm [lowerSumsFourthEffect, BitVec.add_zero]

def lowerSumsBytes : List UInt8 :=
  lowerSumsFirstBytes ++ lowerSumsSecondBytes ++ lowerSumsThirdBytes ++ lowerSumsFourthBytes

def lowerSumsPrefixEffect : RamState → Effect := Effect.seq lowerSumsFirstEffect lowerSumsSecondEffect

def lowerSumsMiddleEffect : RamState → Effect := Effect.seq lowerSumsPrefixEffect lowerSumsThirdEffect

def lowerSumsEffect : RamState → Effect := Effect.seq lowerSumsMiddleEffect lowerSumsFourthEffect

theorem lowerSumsFirst_local : Effect.Local lowerSumsFirstEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [lowerSumsFirstEffect, h.read_reg]
  · intro s
    simp [lowerSumsFirstEffect, Write.Full, Operand.Full]

theorem lowerSumsSecond_local : Effect.Local lowerSumsSecondEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [lowerSumsSecondEffect, rspOf, h.read_reg, h.read_mem]
  · intro s
    simp [lowerSumsSecondEffect, Write.Full, Operand.Full]

theorem lowerSumsThird_local : Effect.Local lowerSumsThirdEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [lowerSumsThirdEffect, rspOf, h.read_reg]
  · intro s
    simp [lowerSumsThirdEffect, Write.Full, Operand.Full]

theorem lowerSumsFourth_local : Effect.Local lowerSumsFourthEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [lowerSumsFourthEffect, savedSource, rspOf, h.read_reg, h.read_mem]
  · intro s
    simp [lowerSumsFourthEffect, Write.Full, Operand.Full]

theorem lowerSums_scratch_after {s t : RamState} {e : Effect} {p : BitVec 64} {n off len : Nat}
    (pre : ScratchPre p n s) (effect : e.Holds s t) (rsp : rspOf t = rspOf s)
    (rip : t.RIP = p + BitVec.ofNat 64 off) (bound : off + len ≤ n) :
    ScratchPre (p + BitVec.ofNat 64 off) len t := by
  refine ⟨rip, ?_, ?_⟩
  · intro c hc
    rw [rsp]
    exact (pre.writable c hc).of_holds effect
  · intro c hc
    rw [rsp]
    exact pre.apart c hc off len bound

theorem lowerSumsBytes_extracted : Extracted.textBytes.toListFrom 0x1c9f6 122 = lowerSumsBytes := by
  decide +kernel

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem lower_sums_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (LowerSumsPre 0x11c9f6 122) (codeRange 0x11c9f6 lowerSumsBytes)
      (Effect.post lowerSumsEffect) := by
  intro s ready loaded pre
  have frame := pre.toScratchPre
  have p1 : ScratchPre 0x11c9f6 13 s :=
    lowerSums_scratch_after (off := 0) frame (Effect.start_holds s) rfl pre.rip (by decide)
  obtain ⟨n1, t1, a1, r1, _, h1⟩ := lower_sums_first boundary hout s ready
    (loaded.mono (codeRange_slice_subset 0x11c9f6 lowerSumsBytes 0 13)) p1
  have sp1 : rspOf t1 = rspOf s := h1.agrees.read
    (by simp [lowerSumsFirstEffect, Effect.components])
  have c1 : CodeIn (codeRange 0x11c9f6 lowerSumsBytes) t1 := h1.codeIn
    (by apply Effect.Avoids.of_noMem; simp [lowerSumsFirstEffect, Effect.components, Component.Covers]) loaded
  have p2 : ScratchPre 0x11ca03 29 t1 :=
    lowerSums_scratch_after (off := 13) frame h1 sp1 h1.rip (by decide)
  obtain ⟨n2, t2, a2, r2, _, h2⟩ := lower_sums_second boundary hout t1 r1
    (c1.mono (codeRange_slice_subset 0x11c9f6 lowerSumsBytes 13 29)) p2
  have sp2 : rspOf t2 = rspOf s := (h2.agrees.read
    (by simp [lowerSumsSecondEffect, Effect.components])).trans sp1
  have h12 : (lowerSumsPrefixEffect s).Holds s t2 :=
    h1.seq lowerSumsSecond_local (lowerSumsFirst_local.full s) h2
  have c2 : CodeIn (codeRange 0x11c9f6 lowerSumsBytes) t2 := h2.codeIn (by
    apply Effect.avoids_codeRange
    have sp := sp1
    x86_norm at sp
    x86_norm [lowerSumsSecondEffect, sp]
    constructor
    · have hf := frame.codeApart 0#64 (by decide)
      rw [BitVec.add_zero] at hf
      exact hf
    · exact frame.codeApart 24#64 (by decide)) c1
  have p3 : ScratchPre 0x11ca20 34 t2 :=
    lowerSums_scratch_after (off := 42) frame h12 sp2 h2.rip (by decide)
  obtain ⟨n3, t3, a3, r3, _, h3⟩ := lower_sums_third boundary hout t2 r2
    (c2.mono (codeRange_slice_subset 0x11c9f6 lowerSumsBytes 42 34)) p3
  have sp3 : rspOf t3 = rspOf s := (h3.agrees.read
    (by simp [lowerSumsThirdEffect, Effect.components])).trans sp2
  have h123 : (lowerSumsMiddleEffect s).Holds s t3 :=
    h12.seq lowerSumsThird_local ((lowerSumsFirst_local.seq lowerSumsSecond_local).full s) h3
  have c3 : CodeIn (codeRange 0x11c9f6 lowerSumsBytes) t3 := h3.codeIn (by
    apply Effect.avoids_codeRange
    have sp := sp2
    x86_norm at sp
    x86_norm [lowerSumsThirdEffect, sp]
    exact frame.codeApart 40#64 (by decide)) c2
  have source1 : savedSource t1 = savedSource s := by
    simp only [savedSource, sp1]
    rw [← (h1.obsAfter (lowerSumsFirst_local.full s) true).read_mem]
    x86_norm [lowerSumsFirstEffect]
  have source2 : savedSource t2 = savedSource t1 := by
    have sp : rspOf t2 = rspOf t1 := sp2.trans sp1.symm
    simp only [savedSource, sp]
    rw [← (h2.obsAfter (lowerSumsSecond_local.full t1) true).read_mem]
    x86_norm [lowerSumsSecondEffect]
  have source3 : savedSource t3 = savedSource s := by
    have sp : rspOf t3 = rspOf t2 := sp3.trans sp2.symm
    have he : savedSource t3 = savedSource t2 := by
      simp only [savedSource, sp]
      rw [← (h3.obsAfter (lowerSumsThird_local.full t2) true).read_mem]
      x86_norm [lowerSumsThirdEffect]
    exact he.trans (source2.trans source1)
  have p4 : LowerSumsPre 0x11ca42 46 t3 := by
    refine ⟨lowerSums_scratch_after (off := 76) frame h123 sp3 h3.rip (by decide), ?_, ?_⟩
    · rw [source3]
      exact pre.left.of_holds h123
    · rw [sp3, source3]
      exact pre.apart
  obtain ⟨n4, t4, a4, r4, _, h4⟩ := lower_sums_fourth boundary hout t3 r3
    (c3.mono (codeRange_slice_subset 0x11c9f6 lowerSumsBytes 76 46)) p4
  have c4 : CodeIn (codeRange 0x11c9f6 lowerSumsBytes) t4 := h4.codeIn (by
    apply Effect.avoids_codeRange
    have sp := sp3
    x86_norm at sp
    x86_norm [lowerSumsFourthEffect, sp]
    exact frame.codeApart 56#64 (by decide)) c3
  exact ⟨n1+n2+n3+n4, t4, ((a1.trans a2).trans a3).trans a4, r4, c4,
    h123.seq lowerSumsFourth_local
      (((lowerSumsFirst_local.seq lowerSumsSecond_local).seq lowerSumsThird_local).full s) h4⟩

end P256.Proofs.Field.Schoolbook
