import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Carry
import P256.Proofs.Common.EffectCompose.Multiply
import P256.Proofs.Common.EffectCompose.Conditions
import P256.Proofs.Common.Encoding.Serialize.Convert.AddLoad
import P256.Proofs.Common.Instructions.ShiftLeft.Compose
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

open P256.Proofs.Common.Instructions (addR64M64Effect)
open P256.Proofs.Common.Instructions.ShiftLeft (shlFlags shlR64Effect)

namespace P256.Proofs.Common.Encoding.Serialize

open X86 X86.Machine X86.UserProcess X86Proofs

@[x86_local] theorem addR64M64Effect_local (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    Effect.Local (addR64M64Effect p dst am) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t ho
    simp only [addR64M64Effect, AddrMode.addr_obs ho, ho.read_reg, ho.read_mem]
  · intro t
    simp [addR64M64Effect, Write.Full, Operand.Full]

attribute [x86_compose] addR64M64Effect shlR64Effect shlFlags

end P256.Proofs.Common.Encoding.Serialize
