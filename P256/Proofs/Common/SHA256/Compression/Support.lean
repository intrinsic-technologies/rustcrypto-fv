import P256.Proofs.Common.SHA256.Compression.Frame
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Encoding.Serialize.Store32
import P256.Proofs.Common.Instructions.Lea32
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
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem store32_legacy_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (valid : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (2 + am.tail.length) (storeAddrAt p am (2 + am.tail.length)) 4)
      (codeRange p (0x89 :: am.modrm reg :: am.tail))
      (CrossPageStore.movM32R32LegacyEffect p (gprNumber 0 0 reg) am) :=
  mov_m32_r32_no_rex_effect_step p reg am valid hx hb

attribute [x86_compose] addR32Imm32Effect shrR32Effect

attribute [x86_compose] Lea32.leaR32Effect

@[x86_local] theorem leaR32Effect_local (p : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (len : Nat) : Effect.Local (Lea32.leaR32Effect p dst am len) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Lea32.leaR32Effect, AddrMode.addr_obs h]
  · intro s
    simp [Lea32.leaR32Effect, Write.Full, Operand.Full]

@[x86_local] theorem addR32Imm32Effect_local (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (imm : BitVec 32) : Effect.Local (addR32Imm32Effect p len dst imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [addR32Imm32Effect, h.read_reg]
  · intro s
    simp [addR32Imm32Effect, Write.Full, Operand.Full]

@[x86_local] theorem shrR32Effect_local (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (count : Nat) : Effect.Local (shrR32Effect p len dst count) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_,
    fun t t' h i hi => ?_, fun t => ?_⟩
  · rfl
  · simp only [shrR32Effect, h.read_reg]
  · rfl
  · cases i <;> simp_all [shrR32Effect, shrFlags, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg] <;>
      split <;> simp_all
  · simp [shrR32Effect, Write.Full, Operand.Full]

end P256.Proofs.Common.SHA256.Compression
