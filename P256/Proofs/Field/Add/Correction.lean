import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
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
import P256.Proofs.Field.Montgomery.Reduction.Slot
import P256.Proofs.Field.Montgomery.Reduction.TailCorrespondence
import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.AddByte
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Field.Add.Arithmetic

set_option autoImplicit false

open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64R64Effect adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Neg64 (negR64Effect neg_rsi_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setccValue setcc_r8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Add

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction
open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [x86_compose] negR64Effect

@[x86_local] theorem negR64Effect_local (p : BitVec 64) (r : BitVec 5) :
    Effect.Local (negR64Effect p r) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [negR64Effect, h.read_reg]
  · intro s
    simp [negR64Effect, Write.Full, Operand.Full]

def correctionInput (s : RamState) : Limbs :=
  ⟨(Operand.reg 0 : Operand 64).read s, (Operand.reg 2 : Operand 64).read s,
   (Operand.reg 8 : Operand 64).read s, (Operand.reg 11 : Operand 64).read s⟩

def correctionValue (s : RamState) : Limbs :=
  correct (correctionInput s) ((Operand.reg 6 : Operand 64).read s)

structure CorrectionCorePre (s : RamState) : Prop where
  rip : s.RIP = 0x113edf
  modulus : (Operand.reg 1 : Operand 64).read s = 0xffffffff00000001

def correctionCoreEffect (s : RamState) : Effect :=
  { rip := 0x113f06
    writes := [⟨(Operand.reg 9 : Operand 64), (correctionValue s).l0⟩,
      ⟨(Operand.reg 10 : Operand 64), (correctionValue s).l1⟩,
      ⟨(Operand.reg 3 : Operand 64), (correctionValue s).l2⟩,
      ⟨(Operand.reg 6 : Operand 64), (correctionValue s).l3⟩,
      ⟨(Operand.reg 0 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def correctionCoreBytes : List UInt8 :=
  [0x49,0x89,0xc1,0x49,0x29,0xf1,0x48,0xf7,0xde,0x41,0x89,0xf2,
   0x31,0xdb,0x49,0x01,0xd2,0x0f,0x92,0xc3,0x48,0x21,0xce,
   0x49,0x39,0xc1,0x49,0x83,0xd2,0,0x4c,0x11,0xc3,0x48,0x89,0xf8,
   0x4c,0x11,0xde]

set_option maxHeartbeats 1000000 in
theorem correctionCore_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CorrectionCorePre (codeRange 0x113edf correctionCoreBytes)
      (Effect.post correctionCoreEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x113edf 0x49 0xc1 (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13ee2 (by decide +kernel))
  advance_then (sub_r64_r64_effect_step 0x113ee2 0x49 0xf1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [subR64R64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ee5 (by decide +kernel))
  advance_then (neg_rsi_effect_step 0x113ee5)
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 6 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [negR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ee8 (by decide +kernel))
  advance_then (mov_r32_r32_rex_effect_step 0x113ee8 0x41 0xf2 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 9 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR32R32Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13eeb (by decide +kernel))
  advance_then (xor_r32_r32_effect_step 0x113eeb 0xdb rfl)
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 12 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [xorR32R32Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13eed (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x113eed 0x49 0xd2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [addR64R64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ef0 (by decide +kernel))
  advance_then_on [StatusFlag.CF] using (setcc_r8_effect_step 0x113ef0 0x92 0xc3 (.inl rfl) rfl (by decide))
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 17 3
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [setccR8Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ef3 (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x113ef3 0x48 0xce (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 20 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [andR64R64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ef6 (by decide +kernel))
  advance_then (cmp_r64_r64_effect_step 0x113ef6 0x49 0xc1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 23 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [cmpR64R64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13ef9 (by decide +kernel))
  advance_then_on [StatusFlag.CF] using (adc_r64_imm8_effect_step 0x113ef9 0x49 0xd2 0 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 26 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64Imm8Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13efd (by decide +kernel))
  advance_then_on [StatusFlag.CF] using (adc_r64_r64_effect_step 0x113efd 0x4c 0xc3 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 30 3
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64R64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f00 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x113f00 0x48 0xf8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 33 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movR64R64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f03 (by decide +kernel))
  advance_then_on [StatusFlag.CF] using (adc_r64_r64_effect_step 0x113f03 0x4c 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113edf correctionCoreBytes 36 3
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [adcR64R64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13f06 (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [correctionCoreEffect]
  · x86_norm [correctionCoreEffect]
    change (correctionValue s).l0 = _ ∧ (correctionValue s).l1 = _ ∧
      (correctionValue s).l2 = _ ∧ (correctionValue s).l3 = _ ∧
      (Operand.reg 7 : Operand 64).read s = _
    dsimp only [gprNumber, rexB, rexR, modrmRm, modrmReg, setccValue, condHolds]
    have zero_byte (b : Bool) :
        mergeGPR 8 (if b then 1#8 else 0#8) 0#64 = BitVec.ofNat 64 b.toNat := by
      cases b <;> rfl
    simp only [BitVec.reduceToNat, BitVec.reduceExtractLsb',
      Nat.reduceShiftLeft, Nat.reduceAdd, UInt8.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
      BitVec.xor_self, BitVec.setWidth_zero, zero_byte,
      adcSpec_ofBool, adcSpec_cf_ofBool, addSpec_cf_carry,
      cmpSpec, subSpec]
    have hm : (Operand.reg 1#5 : Operand 64).read s = 0xffffffff00000001#64 := hP.modulus
    rw [hm]
    simp only [correctionValue, correctionInput, correct, BitVec.lt_def,
      BitVec.and_comm, and_true]
    repeat' constructor
  · intro i
    cases i <;> x86_norm [correctionCoreEffect]
  · x86_norm [correctionCoreEffect]
    repeat' constructor

theorem correctionCoreBytes_code :
    P256.Spec.Program.Extracted.textBytes.toListFrom 0x13edf 39 = correctionCoreBytes := by
  decide +kernel

end P256.Proofs.Field.Add
