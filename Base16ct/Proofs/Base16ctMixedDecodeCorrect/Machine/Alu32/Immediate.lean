import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple
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
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open X86 X86.Machine X86.UserProcess X86Proofs

attribute [x86_compose] addR32Imm8Effect addR32Imm32Effect decR32Effect

@[x86_local] theorem addR32Imm8Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {imm : BitVec 8} : Effect.Local (addR32Imm8Effect p len dst imm) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_,
    fun t t' h i hi => ?_, fun t => ?_⟩
  · rfl
  · simp only [addR32Imm8Effect, h.read_reg]
  · rfl
  · cases i <;> simp_all [addR32Imm8Effect, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg]
  · simp [addR32Imm8Effect, Write.Full, Operand.Full]

@[x86_local] theorem addR32Imm32Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {imm : BitVec 32} : Effect.Local (addR32Imm32Effect p len dst imm) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_,
    fun t t' h i hi => ?_, fun t => ?_⟩
  · rfl
  · simp only [addR32Imm32Effect, h.read_reg]
  · rfl
  · cases i <;> simp_all [addR32Imm32Effect, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg]
  · simp [addR32Imm32Effect, Write.Full, Operand.Full]

@[x86_local] theorem decR32Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} : Effect.Local (decR32Effect p len dst) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_,
    fun t t' h i hi => ?_, fun t => ?_⟩
  · rfl
  · simp only [decR32Effect, h.read_reg]
  · rfl
  · cases i <;> simp_all [decR32Effect, decSpec, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg]
  · simp [decR32Effect, Write.Full, Operand.Full]

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
