import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Field.Schoolbook.Frame
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Instructions (addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect_avoids mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect_avoids adcR64M64Effect_avoids adcR64R64Effect_avoids adcSpec adc_r64_imm8_effect_step adc_r64_m64_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Common.Field
open P256.Proofs.Common.Field.Montgomery.Schoolbook
open P256.Spec.Program.Routines

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem addSpec_fst64 (a b : BitVec 64) : (addSpec a b).1 = a+b := rfl

attribute [local x86_compose] addSpec_fst64

def upperSumsLowBytes : List UInt8 :=
  [0x4c, 0x3, 0x14, 0x24, 0x48, 0x11, 0xce, 0x48, 0x83, 0xd3, 0x0, 0x4c, 0x1, 0xc6, 0x48, 0x83, 0xd3, 0x0, 0x48, 0x3, 0x74, 0x24, 0x8, 0x4c, 0x13, 0x4c, 0x24, 0x20, 0x48, 0x83, 0xd5, 0x0]

def upperSumsLowEffect (s : RamState) : Effect :=
  let v0 := addSpec ((Operand.reg 10 : Operand 64).read s) ((Operand.mem (rspOf s+0#64) : Operand 64).read s)
  let v1 := adcSpec ((Operand.reg 6 : Operand 64).read s) ((Operand.reg 1 : Operand 64).read s) (BitVec.ofBool v0.2.CF)
  let v2 := adcSpec ((Operand.reg 3 : Operand 64).read s) 0#64 (BitVec.ofBool v1.2.CF)
  let v3 := addSpec v1.1 ((Operand.reg 8 : Operand 64).read s)
  let v4 := adcSpec v2.1 0#64 (BitVec.ofBool v3.2.CF)
  let v5 := addSpec v3.1 ((Operand.mem (rspOf s+8#64) : Operand 64).read s)
  let v6 := adcSpec ((Operand.reg 9 : Operand 64).read s) ((Operand.mem (rspOf s+32#64) : Operand 64).read s) (BitVec.ofBool v5.2.CF)
  let v7 := adcSpec ((Operand.reg 5 : Operand 64).read s) 0#64 (BitVec.ofBool v6.2.CF)
  { rip := 0x11caee
    writes := [ ⟨(Operand.reg 10 : Operand 64), v0.1⟩,
      ⟨(Operand.reg 6 : Operand 64), v5.1⟩,
      ⟨(Operand.reg 3 : Operand 64), v4.1⟩,
      ⟨(Operand.reg 9 : Operand 64), v6.1⟩,
      ⟨(Operand.reg 5 : Operand 64), v7.1⟩]
    flags := some (.ofStatusFlags v7.2) }

theorem upperSumsLowBytes_extracted :
    Extracted.textBytes.toListFrom 0x1cace 32 = upperSumsLowBytes := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem upper_sums_low [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (ScratchPre 0x11cace 32)
      (codeRange 0x11cace upperSumsLowBytes) (Effect.post upperSumsLowEffect) := by
  advance_begin (add_r64_m64_effect_step 0x11cace 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    schoolbook_frame
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1cad2 (by decide))
  refine AdvanceTriple.block_then_on ?k0 (adc_r64_r64_effect_step 0x11cad2 0x48 0xce (by simp [RexWPrefix]) (by decide +kernel)) [.CF] ?loc0 ?sub0 ?full0 ?known0 ?mid0
  case loc0 => simp (config := { decide := true }) only [x86_local_on]
  case sub0 => exact codeRange_slice_subset 0x11cace upperSumsLowBytes 4 3
  case full0 => x86_full
  case known0 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid0 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact adcR64R64Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cad5 (by decide))
  case' k0 => x86_norm
  refine AdvanceTriple.block_then_on ?k1 (adc_r64_imm8_effect_step 0x11cad5 0x48 0xd3 0 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) [.CF] ?loc1 ?sub1 ?full1 ?known1 ?mid1
  case loc1 => simp (config := { decide := true }) only [x86_local_on]
  case sub1 => exact codeRange_slice_subset 0x11cace upperSumsLowBytes 7 4
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
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cad9 (by decide))
  case' k1 => x86_norm
  refine AdvanceTriple.block_then ?k2 (add_r64_r64_effect_step 0x11cad9 0x4c 0xc6 (by simp [RexWPrefix]) (by decide +kernel)) ?loc2 ?sub2 ?full2 ?mid2
  case loc2 => x86_local
  case sub2 => exact codeRange_slice_subset 0x11cace upperSumsLowBytes 11 3
  case full2 => x86_full
  case mid2 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact addR64R64Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cadc (by decide))
  case' k2 => x86_norm
  refine AdvanceTriple.block_then_on ?k3 (adc_r64_imm8_effect_step 0x11cadc 0x48 0xd3 0 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) [.CF] ?loc3 ?sub3 ?full3 ?known3 ?mid3
  case loc3 => simp (config := { decide := true }) only [x86_local_on]
  case sub3 => exact codeRange_slice_subset 0x11cace upperSumsLowBytes 14 4
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
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cae0 (by decide))
  case' k3 => x86_norm
  refine AdvanceTriple.block_then ?k4 (add_r64_m64_effect_step 0x11cae0 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl) ?loc4 ?sub4 ?full4 ?mid4
  case loc4 => x86_local
  case sub4 => exact codeRange_slice_subset 0x11cace upperSumsLowBytes 18 5
  case full4 => x86_full
  case mid4 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      schoolbook_frame
    · apply Effect.Avoids.of_noMem
      simp [addR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cae5 (by decide))
  case' k4 => x86_norm
  refine AdvanceTriple.block_then_on ?k5 (adc_r64_m64_effect_step 0x11cae5 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl) [.CF] ?loc5 ?sub5 ?full5 ?known5 ?mid5
  case loc5 => simp (config := { decide := true }) only [x86_local_on]
  case sub5 => exact codeRange_slice_subset 0x11cace upperSumsLowBytes 23 5
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
    · exact adcR64M64Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1caea (by decide))
  case' k5 => x86_norm
  refine AdvanceTriple.block_then_on ?k6 (adc_r64_imm8_effect_step 0x11caea 0x48 0xd5 0 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) [.CF] ?loc6 ?sub6 ?full6 ?known6 ?mid6
  case loc6 => simp (config := { decide := true }) only [x86_local_on]
  case sub6 => exact codeRange_slice_subset 0x11cace upperSumsLowBytes 28 4
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
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1caee (by decide))
  case' k6 => x86_norm
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [upperSumsLowEffect]
  · x86_norm [upperSumsLowEffect] <;> (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · intro i; cases i <;> x86_norm [upperSumsLowEffect] <;> (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · x86_norm [upperSumsLowEffect]

def upperSumsMiddleBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x28, 0x49, 0xf7, 0xe6, 0x48, 0x89, 0xd1, 0x49, 0x89, 0xc0, 0x49, 0x1, 0xd8, 0x48, 0x83, 0xd1, 0x0, 0x4d, 0x1, 0xd8, 0x48, 0x83, 0xd1, 0x0, 0x4d, 0x1, 0xc8, 0x48, 0x83, 0xd5, 0x0, 0x48, 0x3, 0x6c, 0x24, 0x30, 0x49, 0x83, 0xd5, 0x0]

def upperSumsMiddleEffect (s : RamState) : Effect :=
  let p1 := ((Operand.mem (rspOf s+40#64) : Operand 64).read s) * ((Operand.reg 14 : Operand 64).read s)
  let h1 := mulHigh64 ((Operand.mem (rspOf s+40#64) : Operand 64).read s) ((Operand.reg 14 : Operand 64).read s)
  let v4 := addSpec p1 ((Operand.reg 3 : Operand 64).read s)
  let v5 := adcSpec h1 0#64 (BitVec.ofBool v4.2.CF)
  let v6 := addSpec v4.1 ((Operand.reg 11 : Operand 64).read s)
  let v7 := adcSpec v5.1 0#64 (BitVec.ofBool v6.2.CF)
  let v8 := addSpec v6.1 ((Operand.reg 9 : Operand 64).read s)
  let v9 := adcSpec ((Operand.reg 5 : Operand 64).read s) 0#64 (BitVec.ofBool v8.2.CF)
  let v10 := addSpec v9.1 ((Operand.mem (rspOf s+48#64) : Operand 64).read s)
  let v11 := adcSpec ((Operand.reg 13 : Operand 64).read s) 0#64 (BitVec.ofBool v10.2.CF)
  { rip := 0x11cb1a
    writes := [ ⟨(Operand.reg 0 : Operand 64), p1⟩,
      ⟨(Operand.reg 2 : Operand 64), h1⟩,
      ⟨(Operand.reg 1 : Operand 64), v7.1⟩,
      ⟨(Operand.reg 8 : Operand 64), v8.1⟩,
      ⟨(Operand.reg 5 : Operand 64), v10.1⟩,
      ⟨(Operand.reg 13 : Operand 64), v11.1⟩]
    flags := some (.ofStatusFlags v11.2) }

theorem upperSumsMiddleBytes_extracted :
    Extracted.textBytes.toListFrom 0x1caee 44 = upperSumsMiddleBytes := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem upper_sums_middle [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (ScratchPre 0x11caee 44)
      (codeRange 0x11caee upperSumsMiddleBytes) (Effect.post upperSumsMiddleEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11caee 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    schoolbook_frame
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1caf3 (by decide))
  refine AdvanceTriple.block_then ?k7 (mul_r64_effect_step 0x11caf3 0x49 0xe6 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) ?loc7 ?sub7 ?full7 ?mid7
  case loc7 => x86_local
  case sub7 => exact codeRange_slice_subset 0x11caee upperSumsMiddleBytes 5 3
  case full7 => x86_full
  case mid7 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact mulR64Effect_avoids _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1caf6 (by decide))
  case' k7 => x86_norm
  refine AdvanceTriple.block_then ?k8 (mov_r64_r64_effect_step 0x11caf6 0x48 0xd1 (by simp [RexWPrefix]) (by decide +kernel)) ?loc8 ?sub8 ?full8 ?mid8
  case loc8 => x86_local
  case sub8 => exact codeRange_slice_subset 0x11caee upperSumsMiddleBytes 8 3
  case full8 => x86_full
  case mid8 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [movR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1caf9 (by decide))
  case' k8 => x86_norm
  refine AdvanceTriple.block_then ?k9 (mov_r64_r64_effect_step 0x11caf9 0x49 0xc0 (by simp [RexWPrefix]) (by decide +kernel)) ?loc9 ?sub9 ?full9 ?mid9
  case loc9 => x86_local
  case sub9 => exact codeRange_slice_subset 0x11caee upperSumsMiddleBytes 11 3
  case full9 => x86_full
  case mid9 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · apply Effect.Avoids.of_noMem
      simp [movR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cafc (by decide))
  case' k9 => x86_norm
  refine AdvanceTriple.block_then ?k10 (add_r64_r64_effect_step 0x11cafc 0x49 0xd8 (by simp [RexWPrefix]) (by decide +kernel)) ?loc10 ?sub10 ?full10 ?mid10
  case loc10 => x86_local
  case sub10 => exact codeRange_slice_subset 0x11caee upperSumsMiddleBytes 14 3
  case full10 => x86_full
  case mid10 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact addR64R64Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1caff (by decide))
  case' k10 => x86_norm
  refine AdvanceTriple.block_then_on ?k11 (adc_r64_imm8_effect_step 0x11caff 0x48 0xd1 0 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) [.CF] ?loc11 ?sub11 ?full11 ?known11 ?mid11
  case loc11 => simp (config := { decide := true }) only [x86_local_on]
  case sub11 => exact codeRange_slice_subset 0x11caee upperSumsMiddleBytes 17 4
  case full11 => x86_full
  case known11 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid11 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb03 (by decide))
  case' k11 => x86_norm
  refine AdvanceTriple.block_then ?k12 (add_r64_r64_effect_step 0x11cb03 0x4d 0xd8 (by simp [RexWPrefix]) (by decide +kernel)) ?loc12 ?sub12 ?full12 ?mid12
  case loc12 => x86_local
  case sub12 => exact codeRange_slice_subset 0x11caee upperSumsMiddleBytes 21 3
  case full12 => x86_full
  case mid12 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact addR64R64Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb06 (by decide))
  case' k12 => x86_norm
  refine AdvanceTriple.block_then_on ?k13 (adc_r64_imm8_effect_step 0x11cb06 0x48 0xd1 0 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) [.CF] ?loc13 ?sub13 ?full13 ?known13 ?mid13
  case loc13 => simp (config := { decide := true }) only [x86_local_on]
  case sub13 => exact codeRange_slice_subset 0x11caee upperSumsMiddleBytes 24 4
  case full13 => x86_full
  case known13 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid13 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb0a (by decide))
  case' k13 => x86_norm
  refine AdvanceTriple.block_then ?k14 (add_r64_r64_effect_step 0x11cb0a 0x4d 0xc8 (by simp [RexWPrefix]) (by decide +kernel)) ?loc14 ?sub14 ?full14 ?mid14
  case loc14 => x86_local
  case sub14 => exact codeRange_slice_subset 0x11caee upperSumsMiddleBytes 28 3
  case full14 => x86_full
  case mid14 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact addR64R64Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb0d (by decide))
  case' k14 => x86_norm
  refine AdvanceTriple.block_then_on ?k15 (adc_r64_imm8_effect_step 0x11cb0d 0x48 0xd5 0 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) [.CF] ?loc15 ?sub15 ?full15 ?known15 ?mid15
  case loc15 => simp (config := { decide := true }) only [x86_local_on]
  case sub15 => exact codeRange_slice_subset 0x11caee upperSumsMiddleBytes 31 4
  case full15 => x86_full
  case known15 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid15 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb11 (by decide))
  case' k15 => x86_norm
  refine AdvanceTriple.block_then ?k16 (add_r64_m64_effect_step 0x11cb11 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl) ?loc16 ?sub16 ?full16 ?mid16
  case loc16 => x86_local
  case sub16 => exact codeRange_slice_subset 0x11caee upperSumsMiddleBytes 35 5
  case full16 => x86_full
  case mid16 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      schoolbook_frame
    · apply Effect.Avoids.of_noMem
      simp [addR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb16 (by decide))
  case' k16 => x86_norm
  refine AdvanceTriple.block_then_on ?k17 (adc_r64_imm8_effect_step 0x11cb16 0x49 0xd5 0 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) [.CF] ?loc17 ?sub17 ?full17 ?known17 ?mid17
  case loc17 => simp (config := { decide := true }) only [x86_local_on]
  case sub17 => exact codeRange_slice_subset 0x11caee upperSumsMiddleBytes 40 4
  case full17 => x86_full
  case known17 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid17 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb1a (by decide))
  case' k17 => x86_norm
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [upperSumsMiddleEffect]
  · x86_norm [upperSumsMiddleEffect] <;> (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · intro i; cases i <;> x86_norm [upperSumsMiddleEffect] <;> (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · x86_norm [upperSumsMiddleEffect]

def upperSumsHighBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x38, 0x49, 0xf7, 0xe6, 0x48, 0x1, 0xc8, 0x48, 0x83, 0xd2, 0x0, 0x4c, 0x1, 0xe0, 0x48, 0x83, 0xd2, 0x0, 0x48, 0x1, 0xe8, 0x49, 0x83, 0xd5, 0x0, 0x4c, 0x3, 0x6c, 0x24, 0x10, 0x49, 0x83, 0xd7, 0x0, 0x49, 0x1, 0xd5]

def upperSumsHighEffect (s : RamState) : Effect :=
  let p1 := ((Operand.mem (rspOf s+56#64) : Operand 64).read s) * ((Operand.reg 14 : Operand 64).read s)
  let h1 := mulHigh64 ((Operand.mem (rspOf s+56#64) : Operand 64).read s) ((Operand.reg 14 : Operand 64).read s)
  let v2 := addSpec p1 ((Operand.reg 1 : Operand 64).read s)
  let v3 := adcSpec h1 0#64 (BitVec.ofBool v2.2.CF)
  let v4 := addSpec v2.1 ((Operand.reg 12 : Operand 64).read s)
  let v5 := adcSpec v3.1 0#64 (BitVec.ofBool v4.2.CF)
  let v6 := addSpec v4.1 ((Operand.reg 5 : Operand 64).read s)
  let v7 := adcSpec ((Operand.reg 13 : Operand 64).read s) 0#64 (BitVec.ofBool v6.2.CF)
  let v8 := addSpec v7.1 ((Operand.mem (rspOf s+16#64) : Operand 64).read s)
  let v9 := adcSpec ((Operand.reg 15 : Operand 64).read s) 0#64 (BitVec.ofBool v8.2.CF)
  let v10 := addSpec v8.1 v5.1
  { rip := 0x11cb43
    writes := [ ⟨(Operand.reg 0 : Operand 64), v6.1⟩,
      ⟨(Operand.reg 2 : Operand 64), v5.1⟩,
      ⟨(Operand.reg 13 : Operand 64), v10.1⟩,
      ⟨(Operand.reg 15 : Operand 64), v9.1⟩]
    flags := some (.ofStatusFlags v10.2) }

theorem upperSumsHighBytes_extracted :
    Extracted.textBytes.toListFrom 0x1cb1a 41 = upperSumsHighBytes := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem upper_sums_high [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (ScratchPre 0x11cb1a 41)
      (codeRange 0x11cb1a upperSumsHighBytes) (Effect.post upperSumsHighEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11cb1a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    schoolbook_frame
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb1f (by decide))
  refine AdvanceTriple.block_then ?k18 (mul_r64_effect_step 0x11cb1f 0x49 0xe6 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) ?loc18 ?sub18 ?full18 ?mid18
  case loc18 => x86_local
  case sub18 => exact codeRange_slice_subset 0x11cb1a upperSumsHighBytes 5 3
  case full18 => x86_full
  case mid18 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact mulR64Effect_avoids _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb22 (by decide))
  case' k18 => x86_norm
  refine AdvanceTriple.block_then ?k19 (add_r64_r64_effect_step 0x11cb22 0x48 0xc8 (by simp [RexWPrefix]) (by decide +kernel)) ?loc19 ?sub19 ?full19 ?mid19
  case loc19 => x86_local
  case sub19 => exact codeRange_slice_subset 0x11cb1a upperSumsHighBytes 8 3
  case full19 => x86_full
  case mid19 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact addR64R64Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb25 (by decide))
  case' k19 => x86_norm
  refine AdvanceTriple.block_then_on ?k20 (adc_r64_imm8_effect_step 0x11cb25 0x48 0xd2 0 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) [.CF] ?loc20 ?sub20 ?full20 ?known20 ?mid20
  case loc20 => simp (config := { decide := true }) only [x86_local_on]
  case sub20 => exact codeRange_slice_subset 0x11cb1a upperSumsHighBytes 11 4
  case full20 => x86_full
  case known20 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid20 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb29 (by decide))
  case' k20 => x86_norm
  refine AdvanceTriple.block_then ?k21 (add_r64_r64_effect_step 0x11cb29 0x4c 0xe0 (by simp [RexWPrefix]) (by decide +kernel)) ?loc21 ?sub21 ?full21 ?mid21
  case loc21 => x86_local
  case sub21 => exact codeRange_slice_subset 0x11cb1a upperSumsHighBytes 15 3
  case full21 => x86_full
  case mid21 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact addR64R64Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb2c (by decide))
  case' k21 => x86_norm
  refine AdvanceTriple.block_then_on ?k22 (adc_r64_imm8_effect_step 0x11cb2c 0x48 0xd2 0 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) [.CF] ?loc22 ?sub22 ?full22 ?known22 ?mid22
  case loc22 => simp (config := { decide := true }) only [x86_local_on]
  case sub22 => exact codeRange_slice_subset 0x11cb1a upperSumsHighBytes 18 4
  case full22 => x86_full
  case known22 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid22 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb30 (by decide))
  case' k22 => x86_norm
  refine AdvanceTriple.block_then ?k23 (add_r64_r64_effect_step 0x11cb30 0x48 0xe8 (by simp [RexWPrefix]) (by decide +kernel)) ?loc23 ?sub23 ?full23 ?mid23
  case loc23 => x86_local
  case sub23 => exact codeRange_slice_subset 0x11cb1a upperSumsHighBytes 22 3
  case full23 => x86_full
  case mid23 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact addR64R64Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb33 (by decide))
  case' k23 => x86_norm
  refine AdvanceTriple.block_then_on ?k24 (adc_r64_imm8_effect_step 0x11cb33 0x49 0xd5 0 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) [.CF] ?loc24 ?sub24 ?full24 ?known24 ?mid24
  case loc24 => simp (config := { decide := true }) only [x86_local_on]
  case sub24 => exact codeRange_slice_subset 0x11cb1a upperSumsHighBytes 25 4
  case full24 => x86_full
  case known24 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid24 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb37 (by decide))
  case' k24 => x86_norm
  refine AdvanceTriple.block_then ?k25 (add_r64_m64_effect_step 0x11cb37 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl) ?loc25 ?sub25 ?full25 ?mid25
  case loc25 => x86_local
  case sub25 => exact codeRange_slice_subset 0x11cb1a upperSumsHighBytes 29 5
  case full25 => x86_full
  case mid25 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      schoolbook_frame
    · apply Effect.Avoids.of_noMem
      simp [addR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb3c (by decide))
  case' k25 => x86_norm
  refine AdvanceTriple.block_then_on ?k26 (adc_r64_imm8_effect_step 0x11cb3c 0x49 0xd7 0 (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) [.CF] ?loc26 ?sub26 ?full26 ?known26 ?mid26
  case loc26 => simp (config := { decide := true }) only [x86_local_on]
  case sub26 => exact codeRange_slice_subset 0x11cb1a upperSumsHighBytes 34 4
  case full26 => x86_full
  case known26 =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm
  case mid26 =>
    intro s t hP hH hO hF
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact adcR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb40 (by decide))
  case' k26 => x86_norm
  refine AdvanceTriple.block_then ?k27 (add_r64_r64_effect_step 0x11cb40 0x49 0xd5 (by simp [RexWPrefix]) (by decide +kernel)) ?loc27 ?sub27 ?full27 ?mid27
  case loc27 => x86_local
  case sub27 => exact codeRange_slice_subset 0x11cb1a upperSumsHighBytes 38 3
  case full27 => x86_full
  case mid27 =>
    intro s t hP hH hO
    refine ⟨?_, ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · exact addR64R64Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cb43 (by decide))
  case' k27 => x86_norm
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [upperSumsHighEffect]
  · x86_norm [upperSumsHighEffect] <;> (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · intro i; cases i <;> x86_norm [upperSumsHighEffect] <;> (repeat first | apply And.intro | exact Or.inl rfl | exact Or.inr rfl | rfl | apply Or.inr)
  · x86_norm [upperSumsHighEffect]

end P256.Proofs.Field.Schoolbook
