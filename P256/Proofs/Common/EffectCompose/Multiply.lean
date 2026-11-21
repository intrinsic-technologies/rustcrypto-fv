import P256.Proofs.Common.EffectCompose
import P256.Proofs.Common.Instructions.Mul
import P256.Proofs.Common.Instructions.Imul
import P256.Proofs.Common.Instructions.Mul.Memory.Triple
import P256.Proofs.Common.Instructions.Imul.Memory.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (imulFlags64 imulR64M64Effect imulR64R64Effect mulFlags64 mulM64Effect mulR64Effect)
open X86Proofs

namespace P256.Proofs.Common.EffectCompose

open X86 X86.Machine X86.UserProcess

@[x86_local] theorem mulR64Effect_local (p : BitVec 64) (src : BitVec 5) : Effect.Local (mulR64Effect p src) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_,
    fun t t' h i hi => ?_, fun t => ?_⟩
  · rfl
  · simp only [mulR64Effect, h.read_reg]
  · rfl
  · cases i <;> simp [mulR64Effect, mulFlags64, Effect.flag, StatusFlagsOutcome.get, h.read_reg]
  · simp [mulR64Effect, Write.Full, Operand.Full]

@[x86_local] theorem imulR64R64Effect_local (p : BitVec 64) (dst src : BitVec 5) :
    Effect.Local (imulR64R64Effect p dst src) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro t t' h
    simp only [imulR64R64Effect, h.read_reg]
  · intro t
    simp [imulR64R64Effect, Write.Full, Operand.Full]

@[x86_local] theorem mulM64Effect_local (p : BitVec 64) (am : AddrMode) :
    Effect.Local (mulM64Effect p am) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [mulM64Effect, AddrMode.addr_obs h, h.read_reg, h.read_mem]
  · intro s
    simp [mulM64Effect, Write.Full, Operand.Full]

@[x86_local] theorem imulR64M64Effect_local (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    Effect.Local (imulR64M64Effect p dst am) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [imulR64M64Effect, AddrMode.addr_obs h, h.read_reg, h.read_mem]
  · intro s
    simp [imulR64M64Effect, Write.Full, Operand.Full]

attribute [x86_compose] mulM64Effect imulR64M64Effect

attribute [x86_compose] mulR64Effect mulFlags64 imulR64R64Effect imulFlags64

end P256.Proofs.Common.EffectCompose
