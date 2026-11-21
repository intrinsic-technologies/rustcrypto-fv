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

open P256.Proofs.Common.Instructions (mulHigh64 mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect_components adcR64M64Effect_components adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_m64_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CrossSumsPre (s : RamState) : Prop where
  rip : s.RIP = 0x11cc07
  readable : ∀ i ∈ ([8] : List (BitVec 64)), MemReadable s (((Operand.reg 4 : Operand 64).read s) + i) 8

def crossSumsBytes : List UInt8 :=
  [0x4d, 0x1, 0xd5, 0x48, 0x13, 0x4c, 0x24, 0x8, 0x49, 0x11, 0xf0, 0x48, 0x83, 0xd5, 0x0, 0x48, 0x1, 0xd9, 0x4d, 0x11, 0xe0, 0x48, 0x83, 0xd5, 0x0, 0x4c, 0x89, 0xf8, 0x49, 0xf7, 0xe6, 0x48, 0x89, 0xd3, 0x49, 0x89, 0xc4, 0x49, 0x1, 0xec, 0x48, 0x83, 0xd3, 0x0]

def crossSumsEffect (s : RamState) : Effect :=
  let v111ba7 := addSpec ((Operand.reg 13 : Operand 64).read s) ((Operand.reg 10 : Operand 64).read s)
  let v111baa := adcSpec ((Operand.reg 1 : Operand 64).read s) ((Operand.mem (((Operand.reg 4 : Operand 64).read s) + 8) : Operand 64).read s) (BitVec.ofBool (v111ba7.2.CF))
  let v111baf := adcSpec ((Operand.reg 8 : Operand 64).read s) ((Operand.reg 6 : Operand 64).read s) (BitVec.ofBool (v111baa.2.CF))
  let v111bb2 := adcSpec ((Operand.reg 5 : Operand 64).read s) (0 : BitVec 64) (BitVec.ofBool (v111baf.2.CF))
  let v111bb6 := addSpec v111baa.1 ((Operand.reg 3 : Operand 64).read s)
  let v111bb9 := adcSpec v111baf.1 ((Operand.reg 12 : Operand 64).read s) (BitVec.ofBool (v111bb6.2.CF))
  let v111bbc := adcSpec v111bb2.1 (0 : BitVec 64) (BitVec.ofBool (v111bb9.2.CF))
  let v111bc3 := ((Operand.reg 15 : Operand 64).read s) * ((Operand.reg 14 : Operand 64).read s)
  let hv111bc3 := mulHigh64 ((Operand.reg 15 : Operand 64).read s) ((Operand.reg 14 : Operand 64).read s)
  let v111bcc := addSpec v111bc3 v111bbc.1
  let v111bcf := adcSpec hv111bc3 (0 : BitVec 64) (BitVec.ofBool (v111bcc.2.CF))
  { rip := 0x11cc33
    writes := [
      ⟨(.reg 0 : Operand 64), v111bc3⟩,
      ⟨(.reg 1 : Operand 64), v111bb6.1⟩,
      ⟨(.reg 2 : Operand 64), hv111bc3⟩,
      ⟨(.reg 3 : Operand 64), v111bcf.1⟩,
      ⟨(.reg 5 : Operand 64), v111bbc.1⟩,
      ⟨(.reg 8 : Operand 64), v111bb9.1⟩,
      ⟨(.reg 12 : Operand 64), v111bcc.1⟩,
      ⟨(.reg 13 : Operand 64), v111ba7.1⟩]
    flags := some (⟨none, none, none, none, none, none⟩) }

set_option maxHeartbeats 1200000 in
theorem crossSums_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CrossSumsPre (codeRange 0x11cc07 crossSumsBytes)
      (Effect.post crossSumsEffect) := by
  advance_begin (add_r64_r64_effect_step 0x11cc07 0x4d 0xd5 (by simp [RexWPrefix]) (by decide))
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc0a (by decide))
  advance_then_on [.CF] using (adc_r64_m64_effect_step 0x11cc0a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 3 5
  case mid =>
    intro s t hP hH hO hF
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [adcR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc0f (by decide))
  advance_then_on [.CF] using (adc_r64_r64_effect_step 0x11cc0f 0x49 0xf0 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 8 3
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc12 (by decide))
  advance_then_on [.CF] using (adc_r64_imm8_effect_step 0x11cc12 0x48 0xd5 0x0 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 11 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc16 (by decide))
  advance_then (add_r64_r64_effect_step 0x11cc16 0x48 0xd9 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 15 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc19 (by decide))
  advance_then_on [.CF] using (adc_r64_r64_effect_step 0x11cc19 0x4d 0xe0 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 18 3
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64R64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc1c (by decide))
  advance_then_on [.CF] using (adc_r64_imm8_effect_step 0x11cc1c 0x48 0xd5 0x0 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 21 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc20 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc20 0x4c 0xf8 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 25 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc23 (by decide))
  advance_then (mul_r64_effect_step 0x11cc23 0x49 0xe6 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 28 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc26 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc26 0x48 0xd3 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 31 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc29 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc29 0x49 0xc4 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 34 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc2c (by decide))
  advance_then (add_r64_r64_effect_step 0x11cc2c 0x49 0xec (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 37 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc2f (by decide))
  advance_then_on [.CF] using (adc_r64_imm8_effect_step 0x11cc2f 0x48 0xd3 0x0 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc07 crossSumsBytes 40 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc33 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [crossSumsEffect]
  · x86_norm [crossSumsEffect]
    repeat first | apply And.intro | rfl
  · intro i; cases i <;> x86_norm [crossSumsEffect] <;> rfl
  · x86_norm [crossSumsEffect]

end P256.Proofs.Sec1.SquareRoot.Square.Wide
