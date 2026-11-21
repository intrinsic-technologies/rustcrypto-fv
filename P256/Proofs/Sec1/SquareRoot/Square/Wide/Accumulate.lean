import P256.Proofs.Sec1.SquareRoot.Square.Wide.Common
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (addR64M64Effect_components add_r64_m64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect_components adcR64M64Effect_components adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_m64_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shldOneResult shldR64R64OneEffect_components shld_r64_r64_one_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure AccumulatePre (s : RamState) : Prop where
  rip : s.RIP = 0x11cc87
  readable : ∀ i ∈ ([8, 16, 24] : List (BitVec 64)), MemReadable s (((Operand.reg 4 : Operand 64).read s) + i) 8

def accumulateBytes : List UInt8 :=
  [0x48, 0x1, 0xc0, 0x48, 0x1, 0xd0, 0x49, 0x11, 0xed, 0x49, 0x83, 0xd3, 0x0, 0x49, 0xf, 0xa4, 0xc8, 0x1, 0x4d, 0x1, 0xd3, 0x4c, 0x13, 0x44, 0x24, 0x18, 0x49, 0x83, 0xd6, 0x0, 0x4c, 0xf, 0xa4, 0xe3, 0x1, 0x48, 0x3, 0x5c, 0x24, 0x8, 0x49, 0x83, 0xd7, 0x0, 0x49, 0x1, 0xf6, 0x48, 0x83, 0xd3, 0x0, 0x4d, 0x11, 0xcf, 0x48, 0x8b, 0x4c, 0x24, 0x10]

def accumulateEffect (s : RamState) : Effect :=
  let v111c27 := addSpec ((Operand.reg 0 : Operand 64).read s) ((Operand.reg 0 : Operand 64).read s)
  let v111c2a := addSpec v111c27.1 ((Operand.reg 2 : Operand 64).read s)
  let v111c2d := adcSpec ((Operand.reg 13 : Operand 64).read s) ((Operand.reg 5 : Operand 64).read s) (BitVec.ofBool (v111c2a.2.CF))
  let v111c30 := adcSpec ((Operand.reg 11 : Operand 64).read s) (0 : BitVec 64) (BitVec.ofBool (v111c2d.2.CF))
  let v111c34 := shldOneResult ((Operand.reg 8 : Operand 64).read s) ((Operand.reg 1 : Operand 64).read s)
  let v111c39 := addSpec v111c30.1 ((Operand.reg 10 : Operand 64).read s)
  let v111c3c := adcSpec v111c34 ((Operand.mem (((Operand.reg 4 : Operand 64).read s) + 24) : Operand 64).read s) (BitVec.ofBool (v111c39.2.CF))
  let v111c41 := adcSpec ((Operand.reg 14 : Operand 64).read s) (0 : BitVec 64) (BitVec.ofBool (v111c3c.2.CF))
  let v111c45 := shldOneResult ((Operand.reg 3 : Operand 64).read s) ((Operand.reg 12 : Operand 64).read s)
  let v111c4a := addSpec v111c45 ((Operand.mem (((Operand.reg 4 : Operand 64).read s) + 8) : Operand 64).read s)
  let v111c4f := adcSpec ((Operand.reg 15 : Operand 64).read s) (0 : BitVec 64) (BitVec.ofBool (v111c4a.2.CF))
  let v111c53 := addSpec v111c41.1 ((Operand.reg 6 : Operand 64).read s)
  let v111c56 := adcSpec v111c4a.1 (0 : BitVec 64) (BitVec.ofBool (v111c53.2.CF))
  let v111c5a := adcSpec v111c4f.1 ((Operand.reg 9 : Operand 64).read s) (BitVec.ofBool (v111c56.2.CF))
  { rip := 0x11ccc2
    writes := [
      ⟨(.reg 0 : Operand 64), v111c2a.1⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.mem (((Operand.reg 4 : Operand 64).read s) + 16) : Operand 64).read s)⟩,
      ⟨(.reg 3 : Operand 64), v111c56.1⟩,
      ⟨(.reg 8 : Operand 64), v111c3c.1⟩,
      ⟨(.reg 11 : Operand 64), v111c39.1⟩,
      ⟨(.reg 13 : Operand 64), v111c2d.1⟩,
      ⟨(.reg 14 : Operand 64), v111c53.1⟩,
      ⟨(.reg 15 : Operand 64), v111c5a.1⟩]
    flags := some (⟨none, none, none, none, none, none⟩) }

set_option maxHeartbeats 1200000 in
theorem accumulate_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary AccumulatePre (codeRange 0x11cc87 accumulateBytes)
      (Effect.post accumulateEffect) := by
  advance_begin (add_r64_r64_effect_step 0x11cc87 0x48 0xc0 (by simp [RexWPrefix]) (by decide))
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc8a (by decide))
  advance_then (add_r64_r64_effect_step 0x11cc8a 0x48 0xd0 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc8d (by decide))
  advance_then_on [.CF] using (adc_r64_r64_effect_step 0x11cc8d 0x49 0xed (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 6 3
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc90 (by decide))
  advance_then_on [.CF] using (adc_r64_imm8_effect_step 0x11cc90 0x49 0xd3 0x0 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 9 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc94 (by decide))
  advance_then (shld_r64_r64_one_effect_step 0x11cc94 0x49 0xc8 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [shldR64R64OneEffect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc99 (by decide))
  advance_then (add_r64_r64_effect_step 0x11cc99 0x4d 0xd3 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc9c (by decide))
  advance_then_on [.CF] using (adc_r64_m64_effect_step 0x11cc9c 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 21 5
  case mid =>
    intro s t hP hH hO hF
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [adcR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cca1 (by decide))
  advance_then_on [.CF] using (adc_r64_imm8_effect_step 0x11cca1 0x49 0xd6 0x0 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 26 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cca5 (by decide))
  advance_then (shld_r64_r64_one_effect_step 0x11cca5 0x4c 0xe3 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [shldR64R64OneEffect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccaa (by decide))
  advance_then (add_r64_m64_effect_step 0x11ccaa 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 35 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [addR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccaf (by decide))
  advance_then_on [.CF] using (adc_r64_imm8_effect_step 0x11ccaf 0x49 0xd7 0x0 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 40 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccb3 (by decide))
  advance_then (add_r64_r64_effect_step 0x11ccb3 0x49 0xf6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 44 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccb6 (by decide))
  advance_then_on [.CF] using (adc_r64_imm8_effect_step 0x11ccb6 0x48 0xd3 0x0 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 47 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccba (by decide))
  advance_then_on [.CF] using (adc_r64_r64_effect_step 0x11ccba 0x4d 0xcf (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 51 3
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccbd (by decide))
  advance_then (mov_r64_m64_effect_step 0x11ccbd 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cc87 accumulateBytes 54 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccc2 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [accumulateEffect]
  · x86_norm [accumulateEffect]
    repeat first | apply And.intro | rfl
  · intro i; cases i <;> x86_norm [accumulateEffect] <;> rfl
  · x86_norm [accumulateEffect]

end P256.Proofs.Sec1.SquareRoot.Square.Wide
