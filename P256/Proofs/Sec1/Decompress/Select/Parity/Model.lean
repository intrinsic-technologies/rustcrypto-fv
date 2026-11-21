import P256.Proofs.Program.Code
import P256.Proofs.Program.Stack
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Sec1Serialize.Conversion.Stage
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.ByteLogic.And
import P256.Proofs.Common.EffectCompose.ByteLogic
import P256.Proofs.Sec1Serialize.Conversion.Arithmetic
import P256.Proofs.Common.Instructions.Carry.Operation

set_option autoImplicit false

open P256.Proofs.Sec1Serialize (canonicalLimb)
open P256.Proofs.Sec1Serialize.Conversion (compilerConversionBV compilerConversionBV_of_montgomeryAt)
open P256.Proofs.Sec1Serialize.Conversion.Montgomery (compilerRoundBV)
open P256.Proofs.Common.Instructions (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.ByteLogic (andR8Imm8Effect and_sil_one_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR32Imm8Effect adcR32Imm8Effect_components adcR32R32Effect adcR32R32Effect_components adcR64Imm8Effect adcR64Imm8Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adcSpec_result adc_r32_imm8_effect_step adc_r32_r32_effect_step adc_r32_r32_rex_effect_step adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte (movzxR32R8Effect movzx_r32_r8_rex_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setccR8Effect_components setcc_r8_effect_step setcc_r8_rex_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect shlR64Effect_components shl_r64_imm8_effect_step)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)
open P256.Proofs.Field (MontgomeryAt)


namespace P256.Proofs.Sec1.Decompress.Select.Parity

open X86Proofs

def first (a0 a1 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 32 :=
  let q := addSpec (a0 <<< 32) a1
  let neg := addSpec (q.1 * 0xffffffffffffffff) q.1
  let ec := adcSpec ((BitVec.ofBool q.2.CF).setWidth 64)
    (mulHigh64 q.1 0xffffffffffffffff) (BitVec.ofBool neg.2.CF)
  let l := addSpec (q.1 * 0xffffffff) (a0 >>> 32)
  let h := adcSpec (mulHigh64 q.1 0xffffffff) 0 (BitVec.ofBool l.2.CF)
  let o0 := addSpec l.1 ec.1
  let o1 := adcSpec h.1 (a0 * 0xffffffff00000001) (BitVec.ofBool o0.2.CF)
  let o2 := adcSpec (q.1.setWidth 32) ((mulHigh64 a0 0xffffffff00000001).setWidth 32)
    (BitVec.ofBool o1.2.CF)
  (o0.1, o1.1, o2.1)

def second (a b : BitVec 64) (c : BitVec 32) (z : BitVec 64) : BitVec 64 × BitVec 32 :=
  let q := addSpec a z
  let neg := addSpec (q.1 * 0xffffffffffffffff) q.1
  let ec := adcSpec ((BitVec.ofBool q.2.CF).setWidth 64)
    (mulHigh64 q.1 0xffffffffffffffff) (BitVec.ofBool neg.2.CF)
  let l := addSpec (q.1 * 0xffffffff) b
  let h := adcSpec ((mulHigh64 q.1 0xffffffff).setWidth 32) 0 (BitVec.ofBool l.2.CF)
  let o0 := addSpec l.1 ec.1
  let o1 := adcSpec h.1 c (BitVec.ofBool o0.2.CF)
  (o0.1, o1.1)

def last (a : BitVec 64) (b : BitVec 32) (z : BitVec 64) : BitVec 32 :=
  let q := addSpec a z
  let neg := addSpec (q.1 * 0xffffffffffffffff) q.1
  let ec := adcSpec ((BitVec.ofBool q.2.CF).setWidth 32)
    ((mulHigh64 q.1 0xffffffffffffffff).setWidth 32) (BitVec.ofBool neg.2.CF)
  ec.1 + q.1.setWidth 32 + b

def value (a0 a1 a2 a3 : BitVec 64) : BitVec 32 :=
  let r1 := first a0 a1
  let r2 := second r1.1 r1.2.1 r1.2.2 a2
  last r2.1 r2.2 a3

theorem addSpec_low {n : Nat} (a b : BitVec n) : (addSpec a b).1 = a+b := rfl

theorem first_eq (a0 a1 : BitVec 64) :
    let r := compilerRoundBV (a0 <<< 32) (a0 >>> 32)
      (a0 * 0xffffffff00000001) (mulHigh64 a0 0xffffffff00000001) a1
    first a0 a1 = (r.1, r.2.1, r.2.2.1.setWidth 32) := by
  dsimp only [first, compilerRoundBV]
  refine Prod.ext (by rfl) ?_
  refine Prod.ext (by rfl) ?_
  simp only [adcSpec_result, addSpec_low, BitVec.setWidth_add _ _ (show 32 ≤ 64 by decide),
    BitVec.setWidth_mul _ _ (show 32 ≤ 64 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide)]
  simp

theorem second_eq (a b c d z : BitVec 64) :
    second a b (c.setWidth 32) z =
      ((compilerRoundBV a b c d z).1, (compilerRoundBV a b c d z).2.1.setWidth 32) := by
  dsimp only [second, compilerRoundBV]
  refine Prod.ext (by rfl) ?_
  simp only [adcSpec_result, BitVec.setWidth_add _ _ (show 32 ≤ 64 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide)]
  rfl

theorem last_eq_low (a b c d z : BitVec 64) :
    (last a (b.setWidth 32) z).setWidth 1 = (compilerRoundBV a b c d z).1.setWidth 1 := by
  dsimp only [last, compilerRoundBV]
  simp only [adcSpec_result, addSpec_low, BitVec.setWidth_add _ _ (show 1 ≤ 32 by decide),
    BitVec.setWidth_add _ _ (show 1 ≤ 64 by decide),
    BitVec.setWidth_mul _ _ (show 1 ≤ 64 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 1 ≤ 32 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 1 ≤ 64 by decide),
    BitVec.setWidth_eq]
  ac_rfl

theorem value_eq_low (a0 a1 a2 a3 : BitVec 64) :
    (value a0 a1 a2 a3).setWidth 1 = (compilerConversionBV a0 a1 a2 a3).1.setWidth 1 := by
  rw [value, first_eq, second_eq]
  exact last_eq_low _ _ _ _ _

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess

def registers : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 14, .flags, .rip]

theorem readMem (s : RamState) (a : BitVec 64) :
    (Operand.mem a : Operand 64).read s = memLoad s.external a 64 := rfl

theorem read32 (s : RamState) (r : BitVec 5) :
    (Operand.reg r : Operand 32).read s = ((Operand.reg r : Operand 64).read s).setWidth 32 := rfl

theorem byte_merge_low (v : BitVec 8) (old : BitVec 64) :
    (mergeGPR 8 v old).setWidth 8 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [mergeGPR, show ¬ (8 = 32) by decide, ite_false, BitVec.getLsbD_setWidth]
  rw [getLsbD_setSlice old 0 8 v i (by omega)]
  simp [hi]

theorem byte_one_parity (v : BitVec 32) :
    ((v.setWidth 8 &&& 1).setWidth 64) = BitVec.ofNat 64 (v.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
    show (1 : BitVec 8).toNat = 1 from rfl]
  have h := Nat.and_two_pow_sub_one_eq_mod (v.toNat % 256) 1
  change v.toNat % 256 &&& 1 = v.toNat % 256 % 2 at h
  rw [h]
  omega


end P256.Proofs.Sec1.Decompress.Select.Parity
