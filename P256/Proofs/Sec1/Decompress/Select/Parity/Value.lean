import P256.Proofs.Sec1.Decompress.Select.Parity.Model

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

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

namespace P256.Proofs.Sec1.Decompress.Select.Parity

theorem value_parity_of_montgomeryAt {s : RamState} {address : BitVec 64} {x : Nat}
    (input : MontgomeryAt s address x) :
    (value (memLoad s.external address 64) (memLoad s.external (address+8) 64)
      (memLoad s.external (address+16) 64) (memLoad s.external (address+24) 64)).toNat % 2 = x % 2 := by
  have h := value_eq_low (memLoad s.external address 64) (memLoad s.external (address+8) 64)
    (memLoad s.external (address+16) 64) (memLoad s.external (address+24) 64)
  have hc := compilerConversionBV_of_montgomeryAt input
  change compilerConversionBV (memLoad s.external address 64) (memLoad s.external (address+8) 64)
    (memLoad s.external (address+16) 64) (memLoad s.external (address+24) 64) = _ at hc
  rw [hc] at h
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, canonicalLimb, Nat.mul_zero, Nat.pow_zero,
    Nat.div_one, BitVec.toNat_ofNat, Nat.reducePow] at hn
  omega

end P256.Proofs.Sec1.Decompress.Select.Parity
