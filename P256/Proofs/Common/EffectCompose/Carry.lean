import P256.Proofs.Common.EffectCompose
import P256.Proofs.Common.Instructions.Carry.Effect
import P256.Proofs.Common.Instructions.Carry.Memory.Effect

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.Carry

open X86 X86.Machine X86.UserProcess X86Proofs

@[x86_local_on] theorem adcR64R64Effect_localOn (p : BitVec 64) (dst src : BitVec 5) :
    P256.Proofs.Common.EffectCompose.Effect.LocalOn [.CF] (adcR64R64Effect p dst src) := by
  apply P256.Proofs.Common.EffectCompose.Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc := hf.cf (by simp)
    simp only [adcR64R64Effect, ho.read_reg, hc]
  · intro t
    simp [adcR64R64Effect, Write.Full, Operand.Full]

@[x86_local_on] theorem adcR64Imm8Effect_localOn (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    P256.Proofs.Common.EffectCompose.Effect.LocalOn [.CF] (adcR64Imm8Effect p dst imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc := hf.cf (by simp)
    simp only [adcR64Imm8Effect, ho.read_reg, hc]
  · intro t
    simp [adcR64Imm8Effect, Write.Full, Operand.Full]

@[x86_local_on] theorem sbbR64R64Effect_localOn (p : BitVec 64) (dst src : BitVec 5) :
    P256.Proofs.Common.EffectCompose.Effect.LocalOn [.CF] (sbbR64R64Effect p dst src) := by
  apply P256.Proofs.Common.EffectCompose.Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc := hf.cf (by simp)
    simp only [sbbR64R64Effect, ho.read_reg, hc]
  · intro t
    simp [sbbR64R64Effect, Write.Full, Operand.Full]

attribute [x86_compose] adcR64R64Effect adcR32R32Effect adcR64Imm8Effect adcR32Imm8Effect sbbR64R64Effect sbbR32R32Effect sbbR64Imm8Effect sbbR32Imm8Effect

@[x86_local_on] theorem adcR64M64Effect_localOn (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    P256.Proofs.Common.EffectCompose.Effect.LocalOn [.CF] (adcR64M64Effect p dst am) := by
  apply P256.Proofs.Common.EffectCompose.Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc := hf.cf (by simp)
    simp only [adcR64M64Effect, AddrMode.addr_obs ho, ho.read_reg, ho.read_mem, hc]
  · intro t
    simp [adcR64M64Effect, Write.Full, Operand.Full]

attribute [x86_compose] adcR64M64Effect sbbR64M64Effect

end P256.Proofs.Common.Instructions.Carry
