import X86Proofs.Program.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import Sha3.Proofs.X86.Instructions.Xor.Triple
import Sha3.Proofs.X86.Instructions.XorLoad.Triple
import Sha3.Proofs.X86.Instructions.MemAlu.Triple
import Sha3.Proofs.X86.Instructions.And.Triple
import Sha3.Proofs.X86.Instructions.Not.Triple
import Sha3.Proofs.X86.Instructions.Rol.Triple
import Sha3.Proofs.X86.Instructions.Add.Imm8.Triple
import Sha3.Proofs.X86.Instructions.Add.Imm32.Triple
import Sha3.Proofs.X86.Instructions.Sub.Imm32.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Imm32.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.NopMem.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

attribute [x86_compose] xorR64R64Effect xorR32R32Effect xorFlags andR64R64Effect
  andFlags notR64Effect rolR64Effect rolFlags StatusFlagsOutcome.ofStatusFlags
  movR64R64Effect movR64M64Effect movLoadLen xorR64M64Effect movM64R64Effect storeAddrAt
  xorMREffect addR64Imm8Effect addR64Imm32Effect subR64Imm32Effect cmpR64Imm32Effect
  popR64Effect retEffect pushR64Effect pushEffect pushAddr stackTop nopEffect nopMemLen

@[x86_compose] theorem stackPtr_eq_operand_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

section

variable {p : BitVec 64} {len : Nat} {dst src : BitVec 5} {c : Nat} {am : AddrMode}
  {imm8 : BitVec 8} {imm32 : BitVec 32}

@[x86_local] theorem xorR64R64Effect_local : Effect.Local (xorR64R64Effect p dst src) := by
  effect_local [xorR64R64Effect]

@[x86_local] theorem xorR32R32Effect_local : Effect.Local (xorR32R32Effect p len dst src) := by
  effect_local [xorR32R32Effect]

@[x86_local] theorem andR64R64Effect_local : Effect.Local (andR64R64Effect p dst src) := by
  effect_local [andR64R64Effect]

@[x86_local] theorem notR64Effect_local : Effect.Local (notR64Effect p dst) := by
  effect_local [notR64Effect]

@[x86_local] theorem rolR64Effect_local : Effect.Local (rolR64Effect p len dst c) := by
  effect_local [rolR64Effect, rolFlags]

@[x86_local] theorem xorR64M64Effect_local : Effect.Local (xorR64M64Effect p dst am) := by
  effect_local [xorR64M64Effect]

@[x86_local] theorem xorMREffect_local : Effect.Local (xorMREffect p len 64 src am) := by
  effect_local [xorMREffect]

@[x86_local] theorem addR64Imm8Effect_local : Effect.Local (addR64Imm8Effect p dst imm8) := by
  effect_local [addR64Imm8Effect]

@[x86_local] theorem addR64Imm32Effect_local : Effect.Local (addR64Imm32Effect p dst imm32) := by
  effect_local [addR64Imm32Effect]

@[x86_local] theorem subR64Imm32Effect_local : Effect.Local (subR64Imm32Effect p dst imm32) := by
  effect_local [subR64Imm32Effect]

@[x86_local] theorem cmpR64Imm32Effect_local : Effect.Local (cmpR64Imm32Effect p dst imm32) := by
  effect_local [cmpR64Imm32Effect]

end

end X86Proofs
