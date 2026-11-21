import Sha2.Proofs.Common.EffectCompose.Memory
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

namespace Sha2.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86Proofs

attribute [x86_compose] addR64Imm32Effect

@[x86_local] theorem addR64Imm32Effect_local (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    Effect.Local (addR64Imm32Effect p dst imm) := by
  apply Sha2.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [addR64Imm32Effect, h.read_reg]
  · intro s
    simp [addR64Imm32Effect, Write.Full, Operand.Full]

end Sha2.Proofs.Common.Instructions
